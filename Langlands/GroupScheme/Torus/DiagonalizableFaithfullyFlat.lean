import Langlands.GroupScheme.Torus.Diagonalizable
import Langlands.GroupScheme.CorepresentedPoints
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-! # Faithful flatness of diagonalizable group algebras along injective lattice maps -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.GroupScheme.Diagonalizable

/-! ### Freeness of group algebras over subgroup algebras -/

section Free

variable {Λ' Λ : Type*} [AddCommGroup Λ'] [AddCommGroup Λ] {g : Λ' →+ Λ}
  (hg : Function.Injective g)

/-- The chosen representative of a coset of the image of `g`. -/
abbrev cosetRep (q : Λ ⧸ g.range) : Λ := Quotient.out q

theorem neg_cosetRep_add_mem (l : Λ) :
    -cosetRep (QuotientAddGroup.mk l : Λ ⧸ g.range) + l ∈ g.range :=
  QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)

/-- The `Λ'`-coordinate of `l` relative to its chosen coset representative. -/
def cosetCoord (l : Λ) : Λ' :=
  (AddMonoidHom.ofInjective hg).symm ⟨_, neg_cosetRep_add_mem l⟩

theorem map_cosetCoord (l : Λ) :
    g (cosetCoord hg l) = -cosetRep (QuotientAddGroup.mk l : Λ ⧸ g.range) + l :=
  AddMonoidHom.apply_ofInjective_symm hg _

theorem cosetRep_add_map_cosetCoord (l : Λ) :
    cosetRep (QuotientAddGroup.mk l : Λ ⧸ g.range) + g (cosetCoord hg l) = l := by
  rw [map_cosetCoord, add_neg_cancel_left]

theorem mk_cosetRep_add (q : Λ ⧸ g.range) (l' : Λ') :
    (QuotientAddGroup.mk (cosetRep q + g l') : Λ ⧸ g.range) = q := by
  rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq',
    (QuotientAddGroup.eq_zero_iff (g l')).2 (AddMonoidHom.mem_range.2 ⟨l', rfl⟩), add_zero]

theorem cosetCoord_cosetRep_add (q : Λ ⧸ g.range) (l' : Λ') :
    cosetCoord hg (cosetRep q + g l') = l' := by
  apply hg
  rw [map_cosetCoord, mk_cosetRep_add, neg_add_cancel_left]

/-- Every element of `Λ` is uniquely a chosen coset representative plus an element of the
image of `g`. -/
def cosetEquiv : Λ ≃ (Λ ⧸ g.range) × Λ' where
  toFun l := (QuotientAddGroup.mk l, cosetCoord hg l)
  invFun p := cosetRep p.1 + g p.2
  left_inv l := cosetRep_add_map_cosetCoord hg l
  right_inv p := by
    rcases p with ⟨q, l'⟩
    exact Prod.ext (mk_cosetRep_add q l') (cosetCoord_cosetRep_add hg q l')

theorem cosetEquiv_symm_apply (p : (Λ ⧸ g.range) × Λ') :
    (cosetEquiv hg).symm p = cosetRep p.1 + g p.2 := rfl

variable (R : Type*) [CommRing R]

/-- The coefficient-level identification `(Λ/gΛ' →₀ R[Λ']) ≃ R[Λ]`, linear over `R`. -/
def cosetLinearEquiv :
    ((Λ ⧸ g.range) →₀ AddMonoidAlgebra R Λ') ≃ₗ[R] AddMonoidAlgebra R Λ :=
  (Finsupp.mapRange.linearEquiv (AddMonoidAlgebra.coeffLinearEquiv R)).trans <|
    (Finsupp.curryLinearEquiv R).symm.trans <|
      (Finsupp.domLCongr (cosetEquiv hg).symm).trans (AddMonoidAlgebra.coeffLinearEquiv R).symm

theorem cosetLinearEquiv_single_single (q : Λ ⧸ g.range) (l' : Λ') (r : R) :
    cosetLinearEquiv hg R (Finsupp.single q (AddMonoidAlgebra.single l' r)) =
      AddMonoidAlgebra.single (cosetRep q + g l') r := by
  simp only [cosetLinearEquiv, LinearEquiv.trans_apply, Finsupp.mapRange.linearEquiv_apply,
    Finsupp.mapRange_single, AddMonoidAlgebra.coeffLinearEquiv_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.curryLinearEquiv_symm_apply, Finsupp.uncurry_single,
    Finsupp.domLCongr_single, AddMonoidAlgebra.coeffLinearEquiv_symm_apply,
    AddMonoidAlgebra.ofCoeff_single, cosetEquiv_symm_apply]

/-- The algebra structure of `R[Λ]` over `R[Λ']` along `g`. -/
abbrev mapDomainAlgebra : Algebra (AddMonoidAlgebra R Λ') (AddMonoidAlgebra R Λ) :=
  (AddMonoidAlgebra.mapDomainRingHom R g).toAlgebra

/-- The `R[Λ']`-linear map sending a basis vector indexed by a coset to its chosen monomial. -/
def cosetLinearMap :
    letI := mapDomainAlgebra (g := g) R
    ((Λ ⧸ g.range) →₀ AddMonoidAlgebra R Λ') →ₗ[AddMonoidAlgebra R Λ'] AddMonoidAlgebra R Λ :=
  letI := mapDomainAlgebra (g := g) R
  Finsupp.linearCombination (AddMonoidAlgebra R Λ')
    fun q => AddMonoidAlgebra.single (cosetRep q) (1 : R)

theorem cosetLinearMap_apply (x : (Λ ⧸ g.range) →₀ AddMonoidAlgebra R Λ') :
    cosetLinearMap (g := g) R x = cosetLinearEquiv hg R x := by
  let _ := mapDomainAlgebra (g := g) R
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single q r =>
    induction r using AddMonoidAlgebra.induction_linear with
    | zero => simp only [Finsupp.single_zero, map_zero]
    | add r s hr hs => rw [Finsupp.single_add, map_add, map_add, hr, hs]
    | single l' a =>
      rw [cosetLinearEquiv_single_single]
      change Finsupp.linearCombination _ _ _ = _
      rw [Finsupp.linearCombination_single, Algebra.smul_def]
      change AddMonoidAlgebra.mapDomain g (AddMonoidAlgebra.single l' a) *
        AddMonoidAlgebra.single (cosetRep q) 1 = _
      rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.single_mul_single, mul_one,
        add_comm]

include hg in
theorem cosetLinearMap_bijective : Function.Bijective (cosetLinearMap (g := g) R) := by
  have h : ⇑(cosetLinearMap (g := g) R) = ⇑(cosetLinearEquiv hg R) :=
    funext (cosetLinearMap_apply hg R)
  rw [h]
  exact (cosetLinearEquiv hg R).bijective

include hg in
/-- `R[Λ]` is a free `R[Λ']`-module along an injective `g`, with basis indexed by `Λ/gΛ'`. -/
theorem free_mapDomainAlgebra :
    letI := mapDomainAlgebra (g := g) R
    Module.Free (AddMonoidAlgebra R Λ') (AddMonoidAlgebra R Λ) :=
  letI := mapDomainAlgebra (g := g) R
  Module.Free.of_equiv (LinearEquiv.ofBijective _ (cosetLinearMap_bijective hg R))

include hg in
/-- Along an injective homomorphism of abelian groups, the induced map of group algebras over
a nonzero commutative ring is faithfully flat. -/
theorem faithfullyFlat_mapDomainRingHom [Nontrivial R] :
    (AddMonoidAlgebra.mapDomainRingHom R g).FaithfullyFlat := by
  let _ := mapDomainAlgebra (g := g) R
  have := free_mapDomainAlgebra hg R
  exact (RingHom.faithfullyFlat_algebraMap_iff).2 inferInstance

end Free

/-! ### The induced morphism of diagonalizable group schemes -/

section Scheme

variable (R : CommRingCat.{u}) {Λ Λ' : Type u} [AddCommGroup Λ] [AddCommGroup Λ'] (g : Λ' →+ Λ)

/-- The algebra map `incl g : R[Λ'] → R[Λ]` is `mapDomain g`. -/
theorem incl_toRingHom : (incl R g).hom.toRingHom = AddMonoidAlgebra.mapDomainRingHom R g :=
  RingHom.ext (incl_apply R g)

/-- The restriction of characters along `g` is classified by `incl g`. -/
theorem homEquiv_symm_restrict_id :
    (grpCorepresentation R Λ').homEquiv.symm
        ((restrict R g).app (algebra R Λ) ((grpCorepresentation R Λ).homEquiv (𝟙 _))) =
      incl R g := by
  have h := homEquiv_symm_restrict R g ((corepresentation R Λ).homEquiv (𝟙 (algebra R Λ)))
  rw [Equiv.symm_apply_apply, Category.comp_id] at h
  exact h

/-- The homomorphism `D(Λ) → D(Λ')` of diagonalizable group schemes induced by `g : Λ' →+ Λ`. -/
abbrev restrictMap : (groupScheme R Λ).toGrp ⟶ (groupScheme R Λ').toGrp :=
  Corepresented.groupSchemeMap (grpCorepresentation R Λ) (grpCorepresentation R Λ') (restrict R g)

/-- The underlying scheme map of `D(Λ) → D(Λ')` is `Spec` of `mapDomain g : R[Λ'] → R[Λ]`. -/
theorem restrictMap_left :
    (restrictMap R g).hom.hom.left =
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom R g)) := by
  rw [Corepresented.groupSchemeMap_hom, ← incl_toRingHom]
  erw [homEquiv_symm_restrict_id]

/-- Along an injective `g`, the morphism `D(Λ) → D(Λ')` over a nonzero ring is flat and
surjective. -/
theorem flat_and_surjective_restrictMap [Nontrivial R] (hg : Function.Injective g) :
    Flat (restrictMap R g).hom.hom.left ∧ Surjective (restrictMap R g).hom.hom.left := by
  rw [restrictMap_left]
  exact (flat_and_surjective_SpecMap_iff _).2 (faithfullyFlat_mapDomainRingHom hg R)

/-- On points, `D(Λ) → D(Λ')` restricts characters along `g`. -/
theorem pointsEquiv_restrictMap {T : Over (Spec R)} (x : T ⟶ (groupScheme R Λ).X)
    (l' : Λ') :
    DFunLike.coe (F := Multiplicative Λ' →* ((algΓ R).obj T).unopˣ)
        (Corepresented.pointsEquiv (functor R Λ') (grpCorepresentation R Λ') T
          (x ≫ (restrictMap R g).hom.hom)) (.ofAdd l') =
      DFunLike.coe (F := Multiplicative Λ →* ((algΓ R).obj T).unopˣ)
        (Corepresented.pointsEquiv (functor R Λ) (grpCorepresentation R Λ) T x) (.ofAdd (g l')) := by
  erw [Corepresented.groupSchemeMap_points]
  rfl

end Scheme

end Langlands.GroupScheme.Diagonalizable
