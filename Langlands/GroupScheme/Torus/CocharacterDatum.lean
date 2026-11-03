import Langlands.GroupScheme.AffineCorepresented
import Langlands.GroupScheme.AffinePoints
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.Torus.Diagonalizable
import Langlands.GroupScheme.Torus.Weights

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CocharacterDatum

set_option backward.isDefEq.respectTransparency false

/-! ### Coordinates of points of an affine group scheme -/

section Coordinates

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- The chosen coordinate algebra of an affine group scheme. -/
abbrev coordAlgebra : CommAlgCat (CommRingCat.of k) := AffineCoordinates.algebra G

/-- The spectrum of the coordinate algebra is the underlying scheme of `G`. -/
def coordIso : (algSpec (CommRingCat.of k)).obj (op (coordAlgebra G)) ≅ G.X :=
  (Grp.forget _).mapIso (AffineCoordinates.groupSchemeIso G)

variable {G}
variable {S S' S'' : Type u} [CommRing S] [Algebra k S] [CommRing S'] [Algebra k S']
  [CommRing S''] [Algebra k S'']

/-- The coordinate algebra map of a point of `G` over a `k`-algebra. -/
def coord (x : Lie.AffinePoints G S) :
    coordAlgebra G ⟶ CommAlgCat.of (CommRingCat.of k) S :=
  (algSpec.fullyFaithful.preimage (x ≫ (coordIso G).inv)).unop

theorem map_coord (x : Lie.AffinePoints G S) :
    (algSpec (CommRingCat.of k)).map (coord x).op ≫ (coordIso G).hom = x := by
  rw [coord, Quiver.Hom.op_unop, Functor.FullyFaithful.map_preimage, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

theorem coord_injective : Function.Injective (coord (G := G) (S := S)) := by
  intro x y h
  rw [← map_coord x, ← map_coord y, h]

theorem coord_affineMap (f : S →ₐ[k] S') (x : Lie.AffinePoints G S) :
    coord (Lie.affineMap G f x) = coord x ≫ CommAlgCat.ofHom f := by
  apply Quiver.Hom.op_inj
  apply algSpec.fullyFaithful.map_injective
  rw [← cancel_mono (coordIso G).hom, map_coord, Lie.affineMap_apply, op_comp,
    Functor.map_comp, Category.assoc, map_coord]

/-- Extension of coefficients along an injective algebra map is injective on points. -/
theorem affineMap_injective (f : S →ₐ[k] S') (hf : Function.Injective f) :
    Function.Injective (Lie.affineMap G f) := by
  intro x y h
  apply coord_injective
  have h' := congrArg coord h
  rw [coord_affineMap, coord_affineMap] at h'
  ext c
  exact hf (congrArg (fun φ => φ.hom c) h')

/-- **Descent of points along an injective algebra map.** A point whose coordinates lie in the
image of an injective algebra map comes from a point over the source. -/
theorem exists_affineMap_eq (f : S →ₐ[k] S') (hf : Function.Injective f)
    (x : Lie.AffinePoints G S') (hx : ∀ c, (coord x).hom c ∈ f.range) :
    ∃ y : Lie.AffinePoints G S, Lie.affineMap G f y = x := by
  let e := AlgEquiv.ofInjective f hf
  let φ : coordAlgebra G →ₐ[k] S :=
    (e.symm : f.range →ₐ[k] S).comp ((coord x).hom.codRestrict f.range hx)
  refine ⟨(algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom φ).op ≫ (coordIso G).hom, ?_⟩
  apply coord_injective
  rw [coord_affineMap]
  have : coord ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom φ).op ≫ (coordIso G).hom) =
      CommAlgCat.ofHom φ := by
    apply Quiver.Hom.op_inj
    apply algSpec.fullyFaithful.map_injective
    rw [← cancel_mono (coordIso G).hom, map_coord]
  rw [this]
  ext c
  change f (e.symm _) = _
  rw [← AlgEquiv.ofInjective_apply f hf, AlgEquiv.apply_symm_apply]
  rfl

end Coordinates

/-! ### Group algebras -/

section GroupAlgebra

variable {k : Type u} [CommRing k] {Λ Λ' : Type u} [AddCommGroup Λ] [AddCommGroup Λ']
variable {S S' : Type u} [CommRing S] [Algebra k S] [CommRing S'] [Algebra k S']

/-- The monomial `X^γ` as a unit of the group algebra. -/
abbrev monomial (S : Type u) [CommRing S] (γ : Λ) : (AddMonoidAlgebra S Λ)ˣ :=
  (AddMonoidAlgebra.of S Λ).toHomUnits (Multiplicative.ofAdd γ)

@[simp] theorem monomial_val (γ : Λ) :
    (monomial S γ : AddMonoidAlgebra S Λ) = AddMonoidAlgebra.single γ 1 := rfl

theorem monomial_add (γ δ : Λ) : monomial S (γ + δ) = monomial S γ * monomial S δ :=
  map_mul (AddMonoidAlgebra.of S Λ).toHomUnits (Multiplicative.ofAdd γ) (Multiplicative.ofAdd δ)

theorem monomial_zero : monomial S (0 : Λ) = 1 :=
  map_one (AddMonoidAlgebra.of S Λ).toHomUnits

theorem monomial_nsmul (n : ℕ) (γ : Λ) : monomial S (n • γ) = monomial S γ ^ n :=
  map_pow (AddMonoidAlgebra.of S Λ).toHomUnits (Multiplicative.ofAdd γ) n

theorem monomial_injective [Nontrivial S] : Function.Injective (monomial (Λ := Λ) S) := by
  intro γ δ h
  have h' := congrArg (fun u : (AddMonoidAlgebra S Λ)ˣ => (u : AddMonoidAlgebra S Λ).coeff γ) h
  classical
  simp only [monomial_val, AddMonoidAlgebra.coeff_single, Finsupp.single_apply] at h'
  by_contra hne
  split_ifs at h' with h1 h2
  · exact hne h2.symm
  · exact one_ne_zero h'
  · exact h1 trivial
  · exact h1 trivial

/-- Changing coefficients commutes with changing exponents. -/
theorem mapAlgHom_comp_mapDomainAlgHom (f : S →ₐ[k] S') (g : Λ →+ Λ') :
    (AddMonoidAlgebra.mapAlgHom Λ' f).comp (AddMonoidAlgebra.mapDomainAlgHom k S g) =
      (AddMonoidAlgebra.mapDomainAlgHom k S' g).comp (AddMonoidAlgebra.mapAlgHom Λ f) := by
  ext <;> simp

theorem mapAlgHom_mapDomainAlgHom (f : S →ₐ[k] S') (g : Λ →+ Λ') (x : AddMonoidAlgebra S Λ) :
    AddMonoidAlgebra.mapAlgHom Λ' f (AddMonoidAlgebra.mapDomainAlgHom k S g x) =
      AddMonoidAlgebra.mapDomainAlgHom k S' g (AddMonoidAlgebra.mapAlgHom Λ f x) :=
  congrArg (fun φ => φ x) (mapAlgHom_comp_mapDomainAlgHom f g)

theorem units_map_mapAlgHom_monomial (f : S →ₐ[k] S') (γ : Λ) :
    Units.map (AddMonoidAlgebra.mapAlgHom Λ f).toMonoidHom (monomial S γ) = monomial S' γ := by
  apply Units.ext
  simp

theorem mapAlgHom_injective (f : S →ₐ[k] S') (hf : Function.Injective f) :
    Function.Injective (AddMonoidAlgebra.mapAlgHom Λ f) := by
  intro x y h
  ext γ
  have := congrArg (fun z : AddMonoidAlgebra S' Λ => z.coeff γ) h
  simp only [AddMonoidAlgebra.coeff_mapAlgHom] at this
  exact hf this

/-- An element whose coefficients lie in the range of an injective algebra map comes from the
source group algebra. -/
theorem exists_mapAlgHom_eq (f : S →ₐ[k] S') (hf : Function.Injective f)
    (x : AddMonoidAlgebra S' Λ) (hx : ∀ γ, x.coeff γ ∈ f.range) :
    ∃ y : AddMonoidAlgebra S Λ, AddMonoidAlgebra.mapAlgHom Λ f y = x := by
  classical
  choose c hc using hx
  have hc' : ∀ γ, f (c γ) = x.coeff γ := hc
  refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.onFinset x.coeff.support c fun γ hγ => ?_), ?_⟩
  · rw [Finsupp.mem_support_iff]
    intro h0
    apply hγ
    apply hf
    rw [hc' γ, h0, map_zero]
  · ext γ
    rw [AddMonoidAlgebra.coeff_mapAlgHom, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.onFinset_apply,
      hc' γ]

end GroupAlgebra

/-! ### Character values -/

section Values

variable {k : Type u} [Field k] {Z : CommGroupScheme (Spec (CommRingCat.of k))}
variable {S S' : Type u} [CommRing S] [Algebra k S] [CommRing S'] [Algebra k S']

theorem characterValue_affineMap (χ : characterLattice Z) (f : S →ₐ[k] S')
    (t : Lie.AffinePoints Z.toGrp S) :
    Lie.characterValue χ (Lie.affineMap Z.toGrp f t) =
      Units.map f.toMonoidHom (Lie.characterValue χ t) := by
  change Gm.affinePointsEquiv _
    (((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op ≫ t) ≫ _) = _
  rw [Category.assoc]
  apply Units.ext
  rw [Gm.affinePointsEquiv_val, Gm.pointsEquiv_naturality]
  change ((Spec.map (CommRingCat.ofHom f.toRingHom)).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of S')).hom) _ =
      f ((Scheme.ΓSpecIso (CommRingCat.of S)).hom _)
  rw [Scheme.ΓSpecIso_naturality]
  rfl

theorem characterValue_mul (χ : characterLattice Z) (t t' : Lie.AffinePoints Z.toGrp S) :
    Lie.characterValue χ (t * t') = Lie.characterValue χ t * Lie.characterValue χ t' := by
  rw [Lie.characterValue, Lie.characterValue, Lie.characterValue, MonObj.mul_comp, map_mul]

theorem characterValue_one (χ : characterLattice Z) :
    Lie.characterValue χ (1 : Lie.AffinePoints Z.toGrp S) = 1 := by
  rw [Lie.characterValue, MonObj.one_comp, map_one]

end Values

/-! ### Cocharacter data -/

section Datum

variable {k : Type u} [Field k] {Z : CommGroupScheme (Spec (CommRingCat.of k))}
variable {Λ : Type u} [AddCommGroup Λ]
variable {S S' : Type u} [CommRing S] [Algebra k S] [CommRing S'] [Algebra k S']

variable (Λ) in
/-- The diagonal `γ ↦ (γ, γ)`. -/
abbrev diagHom : Λ →+ Λ × Λ := (AddMonoidHom.id Λ).prod (AddMonoidHom.id Λ)

/-- Exponent change along an additive map, on points with coefficients in a group algebra. -/
abbrev expMap (S : Type u) [CommRing S] [Algebra k S] {Λ Λ' : Type u} [AddCommGroup Λ]
    [AddCommGroup Λ'] (g : Λ →+ Λ') :
    Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ) →* Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ') :=
  Lie.affineMap Z.toGrp (AddMonoidAlgebra.mapDomainAlgHom k S g)

/-- Coefficient change along an algebra map, on points with coefficients in a group algebra. -/
abbrev coeffMap (f : S →ₐ[k] S') :
    Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ) →* Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S' Λ) :=
  Lie.affineMap Z.toGrp (AddMonoidAlgebra.mapAlgHom Λ f)

theorem coeffMap_expMap (f : S →ₐ[k] S') {Λ' : Type u} [AddCommGroup Λ'] (g : Λ →+ Λ')
    (p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ)) :
    coeffMap f (expMap S g p) = expMap S' g (coeffMap f p) := by
  rw [coeffMap, expMap, ← Lie.affineMap_comp, mapAlgHom_comp_mapDomainAlgHom, Lie.affineMap_comp]

/-- A point over `S[Λ]` is **multiplicative** if it is a homomorphism from the diagonalizable
group of `Λ`: its image under the diagonal is the product of its images under the two
inclusions `Λ → Λ × Λ`. -/
def IsMult (p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ)) : Prop :=
  expMap S (diagHom Λ) p = expMap S (AddMonoidHom.inl Λ Λ) p * expMap S (AddMonoidHom.inr Λ Λ) p

/-- A **cocharacter datum** of weight `m` for the character `χ`: a multiplicative point over
`S[Λ]` on which `χ` takes the value `X^m`. -/
structure IsDatum (χ : characterLattice Z) (m : Λ) (p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ)) :
    Prop where
  mult : IsMult p
  value : Lie.characterValue χ p = monomial S m

theorem IsMult.coeff_map {p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ)} (hp : IsMult p)
    (f : S →ₐ[k] S') : IsMult (coeffMap f p) := by
  rw [IsMult, ← coeffMap_expMap, ← coeffMap_expMap, ← coeffMap_expMap, hp, map_mul]

theorem IsMult.of_coeff_map [IsAffine Z.toGrp.X.left] {p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ)}
    (f : S →ₐ[k] S') (hf : Function.Injective f) (hp : IsMult (coeffMap f p)) : IsMult p := by
  apply affineMap_injective _ (mapAlgHom_injective (Λ := Λ × Λ) f hf)
  change coeffMap f _ = coeffMap f _
  rw [map_mul, coeffMap_expMap, coeffMap_expMap, coeffMap_expMap]
  exact hp

theorem IsDatum.coeff_map {χ : characterLattice Z} {m : Λ}
    {p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ)} (hp : IsDatum χ m p) (f : S →ₐ[k] S') :
    IsDatum χ m (coeffMap f p) where
  mult := hp.mult.coeff_map f
  value := by
    rw [characterValue_affineMap, hp.value, units_map_mapAlgHom_monomial]

theorem IsDatum.of_coeff_map [IsAffine Z.toGrp.X.left] {χ : characterLattice Z} {m : Λ}
    {p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ)} (f : S →ₐ[k] S')
    (hf : Function.Injective f) (hp : IsDatum χ m (coeffMap f p)) : IsDatum χ m p where
  mult := hp.mult.of_coeff_map f hf
  value := by
    have h := hp.value
    rw [characterValue_affineMap, ← units_map_mapAlgHom_monomial f] at h
    exact Units.map_injective (f := (AddMonoidAlgebra.mapAlgHom Λ f).toMonoidHom)
      (mapAlgHom_injective f hf) h

theorem isMult_one : IsMult (1 : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ)) := by
  rw [IsMult, map_one, map_one, map_one, mul_one]

theorem IsMult.mul {p p' : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ)} (hp : IsMult p)
    (hp' : IsMult p') : IsMult (p * p') := by
  rw [IsMult, map_mul, map_mul, map_mul, hp, hp', mul_mul_mul_comm]

theorem IsMult.inv {p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ)} (hp : IsMult p) :
    IsMult p⁻¹ := by
  rw [IsMult, map_inv, map_inv, map_inv, hp, mul_inv]

theorem isDatum_one (χ : characterLattice Z) :
    IsDatum χ (0 : Λ) (1 : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ)) where
  mult := isMult_one
  value := by rw [characterValue_one, monomial_zero]

theorem IsDatum.mul {χ : characterLattice Z} {m m' : Λ}
    {p p' : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ)} (hp : IsDatum χ m p)
    (hp' : IsDatum χ m' p') : IsDatum χ (m + m') (p * p') where
  mult := hp.mult.mul hp'.mult
  value := by rw [characterValue_mul, hp.value, hp'.value, monomial_add]

theorem IsDatum.prod {J : Type*} (s : Finset J) {χ : characterLattice Z} (m : J → Λ)
    (p : J → Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ)) (hp : ∀ i ∈ s, IsDatum χ (m i) (p i)) :
    IsDatum χ (∑ i ∈ s, m i) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isDatum_one χ
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (hp i (Finset.mem_insert_self i s)).mul
      (ih fun j hj => hp j (Finset.mem_insert_of_mem hj))

/-- Exponent maps add: for a multiplicative point, `[g₁ + g₂]_* p = [g₁]_* p · [g₂]_* p`. -/
theorem IsMult.expMap_add {p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ)} (hp : IsMult p)
    (g₁ g₂ : Λ →+ Λ) : expMap S (g₁ + g₂) p = expMap S g₁ p * expMap S g₂ p := by
  have h := congrArg (expMap S (g₁.coprod g₂)) hp
  rw [map_mul, expMap, expMap, expMap, expMap, ← Lie.affineMap_comp, ← Lie.affineMap_comp,
    ← Lie.affineMap_comp, ← AddMonoidAlgebra.mapDomainAlgHom_comp,
    ← AddMonoidAlgebra.mapDomainAlgHom_comp, ← AddMonoidAlgebra.mapDomainAlgHom_comp] at h
  have h1 : (g₁.coprod g₂).comp (diagHom Λ) = g₁ + g₂ := by
    ext γ; simp
  have h2 : (g₁.coprod g₂).comp (AddMonoidHom.inl Λ Λ) = g₁ := by
    ext γ; simp
  have h3 : (g₁.coprod g₂).comp (AddMonoidHom.inr Λ Λ) = g₂ := by
    ext γ; simp
  rw [h1, h2, h3] at h
  exact h

/-- For a multiplicative point, `[n]_* p = pⁿ`. -/
theorem IsMult.expMap_nsmul {p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ)} (hp : IsMult p)
    (n : ℕ) : expMap S (n • AddMonoidHom.id Λ) p = p ^ n := by
  induction n with
  | zero =>
    have h := hp.expMap_add 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact (mul_eq_left.mp h.symm)
  | succ n ih =>
    rw [succ_nsmul, hp.expMap_add, ih, pow_succ]
    congr 1
    simp [expMap]

theorem expMap_nsmul_injective [IsAffine Z.toGrp.X.left] [IsAddTorsionFree Λ] {n : ℕ}
    (hn : n ≠ 0) : Function.Injective (expMap (Z := Z) S (n • AddMonoidHom.id Λ)) := by
  apply affineMap_injective
  have hinj : Function.Injective (n • AddMonoidHom.id Λ) := fun γ δ h =>
    nsmul_right_injective hn (by simpa using h)
  intro x y h
  rw [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomainAlgHom_apply] at h
  exact AddMonoidAlgebra.mapDomain_injective hinj h

end Datum

/-! ### From a multiplicative point over `k[Λ]` to a homomorphism -/

section Construction

variable {k : Type u} [Field k] {Z : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffine Z.toGrp.X.left] {Λ : Type u} [AddCommGroup Λ]

/-- Points of `Z`, as values of the chosen corepresented point functor of `Z`. -/
def toFunctor (S : CommAlgCat (CommRingCat.of k)) :
    GroupScheme.affinePoints Z.toGrp S →* (AffineCoordinates.functor Z.toGrp).obj S :=
  (Corepresented.affinePointsEquiv _ (AffineCoordinates.corepresentation Z.toGrp) S).toMonoidHom.comp
    (GroupScheme.affinePointsTarget Z.toGrp (AffineCoordinates.groupSchemeIso Z.toGrp).inv S)

theorem toFunctor_injective (S : CommAlgCat (CommRingCat.of k)) :
    Function.Injective (toFunctor (Z := Z) S) := by
  intro x y h
  have h' := (Corepresented.affinePointsEquiv _ (AffineCoordinates.corepresentation Z.toGrp) S).injective h
  change x ≫ (coordIso Z.toGrp).inv = y ≫ (coordIso Z.toGrp).inv at h'
  rwa [cancel_mono] at h'

theorem toFunctor_naturality {S T : CommAlgCat (CommRingCat.of k)} (g : S ⟶ T)
    (x : GroupScheme.affinePoints Z.toGrp S) :
    toFunctor T (GroupScheme.affinePointMap Z.toGrp g x) =
      (AffineCoordinates.functor Z.toGrp).map g (toFunctor S x) := by
  change Corepresented.affinePointsEquiv (AffineCoordinates.functor Z.toGrp)
      (AffineCoordinates.corepresentation Z.toGrp) T
      (((algSpec (CommRingCat.of k)).map g.op ≫ x) ≫ (coordIso Z.toGrp).inv) = _
  rw [Category.assoc, Corepresented.affinePointsEquiv_naturality]
  rfl

theorem toFunctor_comp_hom {S : CommAlgCat (CommRingCat.of k)}
    (y : (algSpec (CommRingCat.of k)).obj (op S) ⟶ (Corepresented.groupScheme
      (AffineCoordinates.functor Z.toGrp) (AffineCoordinates.corepresentation Z.toGrp)).X) :
    toFunctor S (y ≫ (AffineCoordinates.groupSchemeIso Z.toGrp).hom.hom.hom) =
      Corepresented.affinePointsEquiv _ (AffineCoordinates.corepresentation Z.toGrp) S y := by
  change Corepresented.affinePointsEquiv (AffineCoordinates.functor Z.toGrp)
      (AffineCoordinates.corepresentation Z.toGrp) S
      ((y ≫ (coordIso Z.toGrp).hom) ≫ (coordIso Z.toGrp).inv) = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable (p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra k Λ))

/-- Specialization of `p` along the algebra map `X^γ ↦ c(γ)` classified by a character
`c : Λ → Sˣ`. -/
def specialize (S : CommAlgCat (CommRingCat.of k)) (c : Multiplicative Λ →* Sˣ) :
    GroupScheme.affinePoints Z.toGrp S :=
  (algSpec _).map (Diagonalizable.lift (CommRingCat.of k) Λ c).op ≫ p

theorem lift_mapDomain {S : CommAlgCat (CommRingCat.of k)} {Λ' : Type u} [AddCommGroup Λ']
    (c : Multiplicative Λ' →* Sˣ) (g : Λ →+ Λ') :
    (Diagonalizable.lift (CommRingCat.of k) Λ' c).hom.comp
        (AddMonoidAlgebra.mapDomainAlgHom k k g) =
      (Diagonalizable.lift (CommRingCat.of k) Λ (c.comp (AddMonoidHom.toMultiplicative g))).hom := by
  apply AddMonoidAlgebra.algHom_ext
  · intro γ
    simp [Diagonalizable.lift]
  · exact Subsingleton.elim _ _

omit [IsAffine Z.toGrp.X.left] in
theorem specialize_mul (hp : IsMult p) (S : CommAlgCat (CommRingCat.of k))
    (c c' : Multiplicative Λ →* Sˣ) :
    specialize p S (c * c') = specialize p S c * specialize p S c' := by
  let L := Diagonalizable.lift (CommRingCat.of k) (Λ × Λ)
    (c.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst Λ Λ)) *
      c'.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd Λ Λ)))
  have h := congrArg (Lie.affineMap Z.toGrp L.hom) hp
  rw [map_mul, expMap, expMap, expMap, ← Lie.affineMap_comp, ← Lie.affineMap_comp,
    ← Lie.affineMap_comp, lift_mapDomain, lift_mapDomain, lift_mapDomain] at h
  have h1 : ((c.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst Λ Λ)) *
      c'.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd Λ Λ))).comp
        (AddMonoidHom.toMultiplicative (diagHom Λ))) = c * c' := by
    ext γ; rfl
  have h2 : ((c.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst Λ Λ)) *
      c'.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd Λ Λ))).comp
        (AddMonoidHom.toMultiplicative (AddMonoidHom.inl Λ Λ))) = c := by
    ext γ; simp
  have h3 : ((c.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst Λ Λ)) *
      c'.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd Λ Λ))).comp
        (AddMonoidHom.toMultiplicative (AddMonoidHom.inr Λ Λ))) = c' := by
    ext γ; simp
  rw [h1, h2, h3] at h
  exact h

omit [IsAffine Z.toGrp.X.left] in
theorem specialize_naturality {S T : CommAlgCat (CommRingCat.of k)} (g : S ⟶ T)
    (c : Multiplicative Λ →* Sˣ) :
    specialize p T ((Diagonalizable.commFunctor (CommRingCat.of k) Λ).map g c) =
      GroupScheme.affinePointMap Z.toGrp g (specialize p S c) := by
  rw [GroupScheme.affinePointMap_apply, specialize, specialize, ← Category.assoc, ← Functor.map_comp,
    ← op_comp]
  congr 3
  apply CommAlgCat.hom_ext
  apply AddMonoidAlgebra.algHom_ext
  · intro γ
    simp [Diagonalizable.lift]
  · exact Subsingleton.elim _ _

omit [IsAffine Z.toGrp.X.left] in
theorem specialize_monomialUnits :
    specialize p (Diagonalizable.algebra (CommRingCat.of k) Λ)
      (Diagonalizable.monomialUnits (CommRingCat.of k) Λ) = p := by
  rw [specialize]
  have : Diagonalizable.lift (CommRingCat.of k) Λ (Diagonalizable.monomialUnits (CommRingCat.of k) Λ) =
      𝟙 _ := by
    apply CommAlgCat.hom_ext
    apply AddMonoidAlgebra.algHom_ext
    · intro γ
      simp [Diagonalizable.lift]
    · exact Subsingleton.elim _ _
  rw [this, op_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The natural homomorphism `Hom(Λ, Sˣ) → Z(S)` given by a multiplicative point `p`. -/
def natOfMult (hp : IsMult p) :
    Diagonalizable.functor (CommRingCat.of k) Λ ⟶ AffineCoordinates.functor Z.toGrp where
  app S := GrpCat.ofHom (MonoidHom.mk' (fun c => toFunctor S (specialize p S c))
    (fun c c' => by rw [specialize_mul p hp, map_mul]))
  naturality S T g := by
    ext c
    change toFunctor T (specialize p T ((Diagonalizable.commFunctor (CommRingCat.of k) Λ).map g c)) =
      (AffineCoordinates.functor Z.toGrp).map g (toFunctor S (specialize p S c))
    rw [specialize_naturality, toFunctor_naturality]

/-- The homomorphism `D(Λ) ⟶ Z` given by a multiplicative point `p` over `k[Λ]`. -/
def homOfMult (hp : IsMult p) : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ Z.toGrp :=
  Corepresented.groupSchemeMap (Diagonalizable.grpCorepresentation (CommRingCat.of k) Λ)
      (AffineCoordinates.corepresentation Z.toGrp) (natOfMult p hp) ≫
    (AffineCoordinates.groupSchemeIso Z.toGrp).hom

/-- The universal point of `D(Λ)` is sent to `p`. -/
theorem id_comp_homOfMult (hp : IsMult p) :
    (𝟙 ((algSpec (CommRingCat.of k)).obj (op (Diagonalizable.algebra (CommRingCat.of k) Λ))) ≫
      (homOfMult p hp).hom.hom : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra k Λ)) = p := by
  apply toFunctor_injective (Diagonalizable.algebra (CommRingCat.of k) Λ)
  rw [homOfMult, Grp.comp_hom_hom, ← Category.assoc, toFunctor_comp_hom,
    Corepresented.groupSchemeMap_affinePoints]
  have h1 : 𝟙 ((algSpec (CommRingCat.of k)).obj (op (Diagonalizable.algebra (CommRingCat.of k) Λ))) =
      (algSpec (CommRingCat.of k)).map (𝟙 (Diagonalizable.algebra (CommRingCat.of k) Λ)).op := by
    rw [op_id, CategoryTheory.Functor.map_id]
  rw [h1, Corepresented.affinePointsEquiv_map]
  have h2 : (Diagonalizable.grpCorepresentation (CommRingCat.of k) Λ).homEquiv
      (𝟙 (Diagonalizable.algebra (CommRingCat.of k) Λ)) =
        Diagonalizable.monomialUnits (CommRingCat.of k) Λ := by
    apply MonoidHom.ext
    intro m
    apply Units.ext
    rfl
  change toFunctor _ (specialize p _ ((Diagonalizable.grpCorepresentation (CommRingCat.of k) Λ).homEquiv
    (𝟙 (Diagonalizable.algebra (CommRingCat.of k) Λ)))) = _
  rw [h2, specialize_monomialUnits]

/-- A homomorphism built from a datum of nonzero weight restricts `χ` nontrivially. -/
theorem characterRestrict_homOfMult_ne_zero {χ : rationalCharacters Z.toGrp} {m : Λ} (hm : m ≠ 0)
    (hp : IsDatum (rationalCharacters.equivCharacterLattice Z χ) m p) :
    characterRestrict (homOfMult p hp.mult) χ ≠ 0 := by
  intro h
  have h1 : 𝟙 ((algSpec (CommRingCat.of k)).obj (op (Diagonalizable.algebra (CommRingCat.of k) Λ))) ≫
      (characterRestrict (homOfMult p hp.mult) χ).toMul.hom.hom = 1 := by
    rw [h]
    exact rationalCharacters.comp_zero _
  rw [characterRestrict_apply, Grp.comp_hom_hom, ← Category.assoc, id_comp_homOfMult] at h1
  have h2 := hp.value
  rw [Lie.characterValue, rationalCharacters.groupHom_equivCharacterLattice, h1, map_one] at h2
  exact hm (monomial_injective (S := k) (h2.symm.trans monomial_zero.symm))

end Construction

/-! ### Restriction along isomorphisms -/

theorem characterRestrict_iso_ne_zero {S : Scheme.{u}} {G H : GroupScheme S} (e : H ≅ G)
    {ψ : rationalCharacters G} (hψ : ψ ≠ 0) : characterRestrict e.hom ψ ≠ 0 := by
  intro h
  apply hψ
  have h' := congrArg (fun f => characterRestrict f ψ) e.inv_hom_id
  simp only [characterRestrict_comp, characterRestrict_id, AddMonoidHom.comp_apply, h, map_zero,
    AddMonoidHom.id_apply] at h'
  exact h'.symm

/-- **Cocharacters from data.** A cocharacter datum of nonzero weight over `k[ℤ]` for `χ` gives a
homomorphism `𝔾_m ⟶ Z` on which `χ` restricts nontrivially. -/
theorem exists_gm_characterRestrict_ne_zero {k : Type u} [Field k]
    {Z : CommGroupScheme (Spec (CommRingCat.of k))} [IsAffine Z.toGrp.X.left]
    {χ : rationalCharacters Z.toGrp} {m : PUnit.{u+1} → ℤ} (hm : m ≠ 0)
    {p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra k (PUnit.{u+1} → ℤ))}
    (hp : IsDatum (rationalCharacters.equivCharacterLattice Z χ) m p) :
    ∃ φ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ Z.toGrp, characterRestrict φ χ ≠ 0 := by
  refine ⟨(splitTorus.gmIso _).hom ≫ (Diagonalizable.splitIso (CommRingCat.of k)
    (AddEquiv.refl (PUnit.{u+1} → ℤ))).inv ≫ homOfMult p hp.mult, ?_⟩
  rw [characterRestrict_comp, AddMonoidHom.comp_apply, characterRestrict_comp,
    AddMonoidHom.comp_apply]
  exact characterRestrict_iso_ne_zero _ (characterRestrict_iso_ne_zero
    (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (PUnit.{u+1} → ℤ))).symm
    (characterRestrict_homOfMult_ne_zero p hm hp))

end Langlands.GroupScheme.CocharacterDatum
