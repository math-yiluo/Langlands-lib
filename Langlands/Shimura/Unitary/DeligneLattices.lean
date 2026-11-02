import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.Shimura.Unitary.DeligneSchemeSplitting
import Mathlib.LinearAlgebra.Complex.Module

/-! # Character and cocharacter lattices of the Deligne torus

The base change `S_ℂ` of the Deligne torus `S = Res_{ℂ/ℝ} 𝔾_m` to `ℂ` is the split torus `𝔾_m²`
through the two root evaluations of the quadratic coordinate. Hence `X^*(S_ℂ) ≃ ℤ²` and
`X_*(S_ℂ) ≃ ℤ²`, the pairing is the dot product, and complex conjugation, acting through the
Galois action of `Gal(ℂ/ℝ)` on the lattices, interchanges the two coordinates.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Shimura.DeligneTorus

open Langlands.GroupScheme

/-! ### Complex structures twisted by conjugation -/

/-- If a complex structure on `A` is twisted by complex conjugation, the two split coordinates of
a quadratic unit are interchanged. -/
theorem splitPointsEquiv_of_conj {A : Type*} [CommRing A] (i₁ i₂ : Algebra ℂ A)
    (h : ∀ c : ℂ, @algebraMap ℂ A _ _ i₂ c = @algebraMap ℂ A _ _ i₁ (starRingEnd ℂ c))
    (z : Points A) :
    @splitPointsEquiv A _ i₂ z = (@splitPointsEquiv A _ i₁ z).swap := by
  have hI : @algebraMap ℂ A _ _ i₂ Complex.I = -@algebraMap ℂ A _ _ i₁ Complex.I := by
    rw [h, Complex.conj_I, map_neg]
  apply Prod.ext <;> apply Units.ext
  · rw [@splitPointsEquiv_fst A _ i₂, Prod.fst_swap, @splitPointsEquiv_snd A _ i₁, hI]
    ring
  · rw [@splitPointsEquiv_snd A _ i₂, Prod.snd_swap, @splitPointsEquiv_fst A _ i₁, hI]
    ring

/-! ### The complex Deligne torus as a commutative group scheme -/

set_option quotPrecheck false in
/-- The base change `S_ℂ` of the Deligne torus, as a commutative group scheme over `Spec ℂ`.
This is a notation rather than an abbreviation, so that statements about `S_ℂ` and the generic
Galois lemmas (stated for `(CommGroupScheme.baseChange (algebraBaseMap k K)).obj T`) have
syntactically equal types; this keeps kernel checking cheap. -/
scoped notation "S_ℂ" => (Langlands.CommGroupScheme.baseChange
  (Langlands.GroupScheme.algebraBaseMap ℝ ℂ)).obj Langlands.Shimura.DeligneTorus.commGroupScheme

theorem complexBaseMap_eq_algebraBaseMap : complexBaseMap = algebraBaseMap ℝ ℂ := rfl

/-- Complex conjugation as an `ℝ`-algebra automorphism of `ℂ`. Mathematically this is
`Complex.conjAe`; it is restated so that its type uses the same `Algebra ℝ ℂ` instance as
`algebraBaseMap ℝ ℂ` above (`Complex.conjAe` is typed with another, definitionally equal,
instance path, and mixing the two makes kernel checking of the Galois lemmas below very
expensive). -/
def conjAlgEquiv : ℂ ≃ₐ[ℝ] ℂ :=
  AlgEquiv.ofRingEquiv (f := starRingAut) fun r => Complex.conj_ofReal r

@[simp]
theorem conjAlgEquiv_apply (z : ℂ) : conjAlgEquiv z = starRingEnd ℂ z := rfl

/-- Points of `S_ℂ` are pairs of global units, by the two root evaluations `z ↦ z(i), z(-i)`. -/
def commPointsEquiv (T : Over (Spec (CommRingCat.of ℂ))) :
    (T ⟶ (S_ℂ).X) ≃* (Γ(T.left, ⊤))ˣ × (Γ(T.left, ⊤))ˣ :=
  complexSplitPointsEquiv T

theorem commPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of ℂ))} (a : T' ⟶ T)
    (x : T ⟶ (S_ℂ).X) :
    commPointsEquiv T' (a ≫ x) =
      Prod.map (Units.map a.left.appTop.hom.toMonoidHom)
        (Units.map a.left.appTop.hom.toMonoidHom) (commPointsEquiv T x) :=
  complexSplitPointsEquiv_naturality a x

/-! ### Complex conjugation on points -/

/-- Changing the `ℂ`-structure of a test scheme by complex conjugation does not change the
underlying real point, hence not its quadratic coordinates. -/
theorem complexPointsEquiv_descentPoint (T : Over (Spec (CommRingCat.of ℂ)))
    (y : T ⟶ (S_ℂ).X) :
    complexPointsEquiv ((Over.map (galoisBaseMap ℝ ℂ conjAlgEquiv)).obj T)
        (descentPoint (algebraBaseMap ℝ ℂ) (galoisBaseMap ℝ ℂ conjAlgEquiv)
          (galoisBaseMap_over ℝ ℂ conjAlgEquiv) commGroupScheme.toGrp T y) =
      complexPointsEquiv T y := by
  change Corepresented.pointsEquiv (R := CommRingCat.of ℝ) functor corepresentableBy _
      (baseChangePointsEquiv (algebraBaseMap ℝ ℂ) groupScheme _
        (descentPoint (algebraBaseMap ℝ ℂ) (galoisBaseMap ℝ ℂ conjAlgEquiv)
          (galoisBaseMap_over ℝ ℂ conjAlgEquiv) groupScheme T y)) =
    Corepresented.pointsEquiv (R := CommRingCat.of ℝ) functor corepresentableBy _
      (baseChangePointsEquiv (algebraBaseMap ℝ ℂ) groupScheme T y)
  rw [baseChangePointsEquiv_descentPoint, Corepresented.pointsEquiv_naturality]
  generalize Corepresented.pointsEquiv (R := CommRingCat.of ℝ) functor corepresentableBy _
    (baseChangePointsEquiv (algebraBaseMap ℝ ℂ) groupScheme T y) = w
  apply Units.ext
  apply QuadraticAlgebra.ext
  · change (𝟙 T.left : T.left ⟶ T.left).appTop.hom _ = _
    rw [Scheme.Hom.id_appTop]
    rfl
  · change (𝟙 T.left : T.left ⟶ T.left).appTop.hom _ = _
    rw [Scheme.Hom.id_appTop]
    rfl

/-- The complex structure of the global sections of a test scheme, after changing its
`ℂ`-structure by complex conjugation, is the old one twisted by conjugation. -/
theorem algebraMap_conj (T : Over (Spec (CommRingCat.of ℂ))) (c : ℂ) :
    @algebraMap ℂ Γ(T.left, ⊤) _ _
        (complexGlobalAlgebra ((Over.map (galoisBaseMap ℝ ℂ conjAlgEquiv)).obj T)) c =
      @algebraMap ℂ Γ(T.left, ⊤) _ _ (complexGlobalAlgebra T) (starRingEnd ℂ c) := by
  change (T.hom ≫ galoisBaseMap ℝ ℂ conjAlgEquiv).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) =
    T.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv (starRingEnd ℂ c))
  rw [Scheme.Hom.comp_appTop]
  exact congrArg T.hom.appTop
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (conjAlgEquiv : ℂ ≃ₐ[ℝ] ℂ).toRingHom)) c).symm

/-- Complex conjugation interchanges the two split coordinates: seen with the conjugated
`ℂ`-structure, the same real point has its coordinates swapped. -/
theorem commPointsEquiv_descentPoint (T : Over (Spec (CommRingCat.of ℂ)))
    (y : T ⟶ (S_ℂ).X) :
    commPointsEquiv ((Over.map (galoisBaseMap ℝ ℂ conjAlgEquiv)).obj T)
        (descentPoint (algebraBaseMap ℝ ℂ) (galoisBaseMap ℝ ℂ conjAlgEquiv)
          (galoisBaseMap_over ℝ ℂ conjAlgEquiv) commGroupScheme.toGrp T y) =
      (commPointsEquiv T y).swap := by
  change @splitPointsEquiv Γ(T.left, ⊤) _
      (complexGlobalAlgebra ((Over.map (galoisBaseMap ℝ ℂ conjAlgEquiv)).obj T))
      (complexPointsEquiv ((Over.map (galoisBaseMap ℝ ℂ conjAlgEquiv)).obj T)
        (descentPoint (algebraBaseMap ℝ ℂ) (galoisBaseMap ℝ ℂ conjAlgEquiv)
          (galoisBaseMap_over ℝ ℂ conjAlgEquiv) commGroupScheme.toGrp T y)) =
    (@splitPointsEquiv Γ(T.left, ⊤) _ (complexGlobalAlgebra T) (complexPointsEquiv T y)).swap
  rw [complexPointsEquiv_descentPoint]
  exact splitPointsEquiv_of_conj _ _ (algebraMap_conj T) _

/-! ### The splitting `S_ℂ ≅ 𝔾_m²` -/

/-- Families indexed by `Fin 2` are pairs, multiplicatively. -/
def finTwoMulEquiv (M : Type*) [Group M] : (Fin 2 → M) ≃* M × M where
  toFun f := (f 0, f 1)
  invFun p := ![p.1, p.2]
  left_inv f := by
    funext i
    fin_cases i <;> rfl
  right_inv p := rfl
  map_mul' f g := rfl

/-- Restriction of pairs of global units along a morphism of test schemes. -/
abbrev pairRestrict {T T' : Over (Spec (CommRingCat.of ℂ))} (a : T' ⟶ T) :
    (Γ(T.left, ⊤))ˣ × (Γ(T.left, ⊤))ˣ →* (Γ(T'.left, ⊤))ˣ × (Γ(T'.left, ⊤))ˣ :=
  (Units.map a.left.appTop.hom.toMonoidHom).prodMap (Units.map a.left.appTop.hom.toMonoidHom)

/-- The coordinates of `𝔾_m²`, as a pair of global units. -/
def splitTorusPairEquiv (T : Over (Spec (CommRingCat.of ℂ))) :
    (T ⟶ (splitTorus (Spec (CommRingCat.of ℂ)) (Fin 2)).X) ≃*
      (Γ(T.left, ⊤))ˣ × (Γ(T.left, ⊤))ˣ :=
  (splitTorus.pointsEquiv (Fin 2) T).trans (finTwoMulEquiv _)

theorem splitTorusPairEquiv_naturality {T T' : Over (Spec (CommRingCat.of ℂ))} (a : T' ⟶ T)
    (y : T ⟶ (splitTorus (Spec (CommRingCat.of ℂ)) (Fin 2)).X) :
    splitTorusPairEquiv T' (a ≫ y) = pairRestrict a (splitTorusPairEquiv T y) := by
  rw [splitTorusPairEquiv, MulEquiv.trans_apply, splitTorus.pointsEquiv_naturality]
  rfl

/-- `S_ℂ ≅ 𝔾_m²` as group schemes over `Spec ℂ`: both have the pairs of global units as natural
point model, by the root evaluations and by the coordinates. -/
def splitTorusGrpIso :
    (S_ℂ).toGrp ≅ splitTorus (Spec (CommRingCat.of ℂ)) (Fin 2) :=
  isoOfPointModels (fun T : Over (Spec (CommRingCat.of ℂ)) => (Γ(T.left, ⊤))ˣ × (Γ(T.left, ⊤))ˣ)
    pairRestrict commPointsEquiv splitTorusPairEquiv
    (fun a x => commPointsEquiv_naturality a x) splitTorusPairEquiv_naturality

/-- `S_ℂ ≅ 𝔾_m²` as commutative group schemes over `Spec ℂ`. -/
def splitTorusIso :
    S_ℂ ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of ℂ)) (Fin 2) where
  hom := Additive.ofMul splitTorusGrpIso.hom
  inv := Additive.ofMul splitTorusGrpIso.inv
  hom_inv_id := congrArg Additive.ofMul splitTorusGrpIso.hom_inv_id
  inv_hom_id := congrArg Additive.ofMul splitTorusGrpIso.inv_hom_id

/-- The splitting sends a point to the family of its two split coordinates. -/
theorem splitTorusIso_hom_points (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ (S_ℂ).X) :
    (splitTorus.pointsEquiv (Fin 2) T
        (x ≫ (CommGroupScheme.groupHom splitTorusIso.hom).hom.hom) 0,
      splitTorus.pointsEquiv (Fin 2) T
        (x ≫ (CommGroupScheme.groupHom splitTorusIso.hom).hom.hom) 1) =
      commPointsEquiv T x :=
  isoOfPointModels_hom (fun T : Over (Spec (CommRingCat.of ℂ)) => (Γ(T.left, ⊤))ˣ × (Γ(T.left, ⊤))ˣ)
    pairRestrict commPointsEquiv splitTorusPairEquiv
    (fun a x => commPointsEquiv_naturality a x) splitTorusPairEquiv_naturality T x

/-- The inverse splitting sends a family of two units to the point with these split
coordinates. -/
theorem commPointsEquiv_splitTorusIso_inv (T : Over (Spec (CommRingCat.of ℂ)))
    (y : T ⟶ (splitTorus (Spec (CommRingCat.of ℂ)) (Fin 2)).X) :
    commPointsEquiv T (y ≫ (CommGroupScheme.groupHom splitTorusIso.inv).hom.hom) =
      (splitTorus.pointsEquiv (Fin 2) T y 0, splitTorus.pointsEquiv (Fin 2) T y 1) :=
  isoOfPointModels_inv (fun T : Over (Spec (CommRingCat.of ℂ)) => (Γ(T.left, ⊤))ˣ × (Γ(T.left, ⊤))ˣ)
    pairRestrict commPointsEquiv splitTorusPairEquiv
    (fun a x => commPointsEquiv_naturality a x) splitTorusPairEquiv_naturality T y

/-! ### The lattices -/

/-- `X^*(S_ℂ) ≃ ℤ²`. The character attached to `(p, q)` is `z ↦ z(i) ^ p * z(-i) ^ q` in the split
coordinates. -/
def characterEquiv : characterLattice S_ℂ ≃+ ℤ × ℤ :=
  ((characterLattice.congr splitTorusIso).trans
    (splitTorus.characterLatticeEquiv ℂ (Fin 2))).trans
      (LinearEquiv.finTwoArrow ℤ ℤ).toAddEquiv

/-- `X_*(S_ℂ) ≃ ℤ²`. The cocharacter attached to `(m, n)` is `s ↦ (s ^ m, s ^ n)` in the split
coordinates. -/
def cocharacterEquiv : cocharacterLattice S_ℂ ≃+ ℤ × ℤ :=
  ((cocharacterLattice.congr splitTorusIso).trans
    (splitTorus.cocharacterLatticeEquiv ℂ (Fin 2))).trans
      (LinearEquiv.finTwoArrow ℤ ℤ).toAddEquiv

theorem characterEquiv_symm_eq (p q : ℤ) :
    characterEquiv.symm (p, q) =
      splitTorusIso.hom ≫ (splitTorus.characterLatticeEquiv ℂ (Fin 2)).symm ![p, q] := rfl

theorem cocharacterEquiv_symm_eq (m n : ℤ) :
    cocharacterEquiv.symm (m, n) =
      (splitTorus.cocharacterLatticeEquiv ℂ (Fin 2)).symm ![m, n] ≫ splitTorusIso.inv := rfl

/-- On points, the character attached to `(p, q)` is `z ↦ z(i) ^ p * z(-i) ^ q`. -/
theorem characterEquiv_symm_points (p q : ℤ) (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ (S_ℂ).X) :
    Gm.pointsEquiv _ T (x ≫ (CommGroupScheme.groupHom (characterEquiv.symm (p, q))).hom.hom) =
      (commPointsEquiv T x).1 ^ p * (commPointsEquiv T x).2 ^ q := by
  rw [characterEquiv_symm_eq, comp_groupHom_comp,
    splitTorus.pointsEquiv_characterLatticeEquiv_symm, Fin.prod_univ_two,
    ← splitTorusIso_hom_points T x]
  rfl

/-- On points, the cocharacter attached to `(m, n)` is `s ↦ (s ^ m, s ^ n)`. -/
theorem cocharacterEquiv_symm_points (m n : ℤ) (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ (Gm (Spec (CommRingCat.of ℂ))).X) :
    commPointsEquiv T (x ≫ (CommGroupScheme.groupHom (cocharacterEquiv.symm (m, n))).hom.hom) =
      (Gm.pointsEquiv _ T x ^ m, Gm.pointsEquiv _ T x ^ n) := by
  rw [cocharacterEquiv_symm_eq, comp_groupHom_comp, commPointsEquiv_splitTorusIso_inv,
    splitTorus.pointsEquiv_cocharacterLatticeEquiv_symm]
  rfl

/-- Under the lattice equivalences the pairing is the dot product on `ℤ²`. -/
theorem latticePairing_eq (χ : characterLattice S_ℂ)
    (ν : cocharacterLattice S_ℂ) :
    latticePairing S_ℂ χ ν =
      (characterEquiv χ).1 * (cocharacterEquiv ν).1 +
        (characterEquiv χ).2 * (cocharacterEquiv ν).2 := by
  rw [← latticePairing_congr splitTorusIso, splitTorus.latticePairing_eq_sum, Fin.sum_univ_two]
  rfl

/-! ### Complex conjugation on the lattices -/

/-- Complex conjugation acts on a character by evaluating it at the same real point, seen with
the conjugated `ℂ`-structure. -/
theorem galoisRepresentation_conj_points (χ : characterLattice S_ℂ)
    (U : Over (Spec (CommRingCat.of ℂ))) (y : U ⟶ (S_ℂ).X) :
    Gm.pointsEquiv _ U (y ≫ (CommGroupScheme.groupHom
        (characterLattice.galoisRepresentation ℝ ℂ commGroupScheme conjAlgEquiv χ)).hom.hom) =
      Gm.pointsEquiv _ ((Over.map (galoisBaseMap ℝ ℂ conjAlgEquiv)).obj U)
        (descentPoint (algebraBaseMap ℝ ℂ) (galoisBaseMap ℝ ℂ conjAlgEquiv)
          (galoisBaseMap_over ℝ ℂ conjAlgEquiv) commGroupScheme.toGrp U y ≫
            (CommGroupScheme.groupHom χ).hom.hom) :=
  characterLattice.galoisRepresentation_points ℝ ℂ commGroupScheme conjAlgEquiv χ U y

theorem characterEquiv_symm_descentPoint_aux (p q : ℤ) (U : Over (Spec (CommRingCat.of ℂ)))
    (y : U ⟶ (S_ℂ).X) :
    Gm.pointsEquiv _ ((Over.map (galoisBaseMap ℝ ℂ conjAlgEquiv)).obj U)
        (descentPoint (algebraBaseMap ℝ ℂ) (galoisBaseMap ℝ ℂ conjAlgEquiv)
          (galoisBaseMap_over ℝ ℂ conjAlgEquiv) commGroupScheme.toGrp U y ≫
            (CommGroupScheme.groupHom (characterEquiv.symm (p, q))).hom.hom) =
      (commPointsEquiv ((Over.map (galoisBaseMap ℝ ℂ conjAlgEquiv)).obj U)
          (descentPoint (algebraBaseMap ℝ ℂ) (galoisBaseMap ℝ ℂ conjAlgEquiv)
            (galoisBaseMap_over ℝ ℂ conjAlgEquiv) commGroupScheme.toGrp U y)).1 ^ p *
        (commPointsEquiv ((Over.map (galoisBaseMap ℝ ℂ conjAlgEquiv)).obj U)
          (descentPoint (algebraBaseMap ℝ ℂ) (galoisBaseMap ℝ ℂ conjAlgEquiv)
            (galoisBaseMap_over ℝ ℂ conjAlgEquiv) commGroupScheme.toGrp U y)).2 ^ q :=
  characterEquiv_symm_points p q _ _

theorem characterEquiv_symm_descentPoint (p q : ℤ) (U : Over (Spec (CommRingCat.of ℂ)))
    (y : U ⟶ (S_ℂ).X) :
    Gm.pointsEquiv _ ((Over.map (galoisBaseMap ℝ ℂ conjAlgEquiv)).obj U)
        (descentPoint (algebraBaseMap ℝ ℂ) (galoisBaseMap ℝ ℂ conjAlgEquiv)
          (galoisBaseMap_over ℝ ℂ conjAlgEquiv) commGroupScheme.toGrp U y ≫
            (CommGroupScheme.groupHom (characterEquiv.symm (p, q))).hom.hom) =
      (commPointsEquiv U y).2 ^ p * (commPointsEquiv U y).1 ^ q := by
  rw [characterEquiv_symm_descentPoint_aux, commPointsEquiv_descentPoint]
  rfl

/-- Complex conjugation sends the character attached to `(p, q)` to the one attached to
`(q, p)`. -/
theorem galoisRepresentation_conj_characterEquiv_symm (p q : ℤ) :
    characterLattice.galoisRepresentation ℝ ℂ commGroupScheme conjAlgEquiv
        (characterEquiv.symm (p, q)) = characterEquiv.symm (q, p) := by
  apply characterLattice.ext_points
  intro U y
  refine (galoisRepresentation_conj_points _ U y).trans ?_
  refine (characterEquiv_symm_descentPoint p q U y).trans ?_
  rw [characterEquiv_symm_points, mul_comm]

/-- Complex conjugation acts on `X^*(S_ℂ) ≃ ℤ²` by interchanging the two coordinates. -/
theorem characterEquiv_galoisRepresentation_conj (χ : characterLattice S_ℂ) :
    characterEquiv (characterLattice.galoisRepresentation ℝ ℂ commGroupScheme conjAlgEquiv χ) =
      (characterEquiv χ).swap := by
  conv_lhs => rw [← characterEquiv.symm_apply_apply χ]
  rw [galoisRepresentation_conj_characterEquiv_symm, AddEquiv.apply_symm_apply]
  rfl

theorem commPointsEquiv_cocharacterEquiv_symm_conj (m n : ℤ) (U : Over (Spec (CommRingCat.of ℂ)))
    (x : U ⟶ (Gm (Spec (CommRingCat.of ℂ))).X) :
    commPointsEquiv ((Over.map (galoisBaseMap ℝ ℂ conjAlgEquiv)).obj U)
        ((Gm.pointsEquiv _ ((Over.map (galoisBaseMap ℝ ℂ conjAlgEquiv)).obj U)).symm
          (Gm.pointsEquiv _ U x) ≫
            (CommGroupScheme.groupHom (cocharacterEquiv.symm (m, n))).hom.hom) =
      (Gm.pointsEquiv _ U x ^ m, Gm.pointsEquiv _ U x ^ n) := by
  rw [cocharacterEquiv_symm_points, MulEquiv.apply_symm_apply]

/-- Complex conjugation sends the cocharacter attached to `(m, n)` to the one attached to
`(n, m)`. -/
theorem galoisRepresentation_conj_cocharacterEquiv_symm (m n : ℤ) :
    cocharacterLattice.galoisRepresentation ℝ ℂ commGroupScheme conjAlgEquiv
        (cocharacterEquiv.symm (m, n)) = cocharacterEquiv.symm (n, m) := by
  apply cocharacterLattice.ext_points
  intro U x
  apply (commPointsEquiv U).injective
  have h := commPointsEquiv_descentPoint U (x ≫ (CommGroupScheme.groupHom
    (cocharacterLattice.galoisRepresentation ℝ ℂ commGroupScheme conjAlgEquiv
      (cocharacterEquiv.symm (m, n)))).hom.hom)
  rw [cocharacterLattice.descentPoint_galoisRepresentation,
    commPointsEquiv_cocharacterEquiv_symm_conj] at h
  have h' := congrArg Prod.swap h
  rw [Prod.swap_swap] at h'
  rw [← h', cocharacterEquiv_symm_points]
  rfl

/-- Complex conjugation acts on `X_*(S_ℂ) ≃ ℤ²` by interchanging the two coordinates. -/
theorem cocharacterEquiv_galoisRepresentation_conj
    (ν : cocharacterLattice S_ℂ) :
    cocharacterEquiv
        (cocharacterLattice.galoisRepresentation ℝ ℂ commGroupScheme conjAlgEquiv ν) =
      (cocharacterEquiv ν).swap := by
  conv_lhs => rw [← cocharacterEquiv.symm_apply_apply ν]
  rw [galoisRepresentation_conj_cocharacterEquiv_symm, AddEquiv.apply_symm_apply]
  rfl

/-- Complex conjugation acts nontrivially on `X^*(S_ℂ)`. -/
theorem characterLattice_galoisRepresentation_conj_ne_one :
    characterLattice.galoisRepresentation ℝ ℂ commGroupScheme conjAlgEquiv ≠ 1 := by
  intro h
  have h' := congrArg characterEquiv
    (LinearMap.congr_fun h (characterEquiv.symm (1, 0)))
  rw [galoisRepresentation_conj_characterEquiv_symm, Module.End.one_apply,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at h'
  simp at h'

end Langlands.Shimura.DeligneTorus
