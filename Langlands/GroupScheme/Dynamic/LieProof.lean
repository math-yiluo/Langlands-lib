import Langlands.GroupScheme.Dynamic.LieStatement
import Langlands.GroupScheme.Dynamic.AffineChart
import Langlands.GroupScheme.Torus.WeightDecomposition

/-! # Lie algebras of dynamic subgroups as sums of weight spaces

This module proves `DynamicLieStatement`. Both sides of each equivalence are read off the
finitely many weight coefficients of a Lie vector `X`: the coefficients of the universal adjoint
vector `Ad(χ(t)) X` over `k[t^{±1}]`, computed with the rank-one split torus `𝔾_m ≅ 𝔾_m^{PUnit}`.
The dynamic subgroups are tested through the coaction of `χ` on the global sections of `G`
(`Dynamic.AffineChart`), and the comparison map `ψ : (k[t^{±1}])[ε] → (k[ε])[T^{±1}]`
identifies the orbit map of `X` with the universal adjoint vector. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.DynamicLie

set_option backward.isDefEq.respectTransparency false

section GmIso

variable (S : Scheme.{u})

theorem gmIso_hom_apply (T : Over S) (x : T ⟶ (Gm S).X) :
    splitTorus.pointsEquiv PUnit T (x ≫ (splitTorus.gmIso S).hom.hom.hom) PUnit.unit =
      Gm.pointsEquiv S T x := by
  rw [splitTorus.gmIso, isoOfPointModels_hom]
  · rfl
  · intro T T' a x
    funext i
    change Gm.pointsEquiv S _ (a ≫ x) = _
    rw [Gm.pointsEquiv_naturality]
    rfl
  · intro T T' a y
    exact splitTorus.pointsEquiv_naturality PUnit a y

theorem gmIso_inv_apply (T : Over S) (y : T ⟶ (splitTorus S PUnit).X) :
    Gm.pointsEquiv S T (y ≫ (splitTorus.gmIso S).inv.hom.hom) =
      splitTorus.pointsEquiv PUnit T y PUnit.unit := by
  rw [← gmIso_hom_apply S T (y ≫ (splitTorus.gmIso S).inv.hom.hom), Category.assoc]
  have h : (splitTorus.gmIso S).inv.hom.hom ≫ (splitTorus.gmIso S).hom.hom.hom = 𝟙 _ :=
    congrArg (fun f : splitTorus S PUnit ⟶ splitTorus S PUnit => f.hom.hom)
      (splitTorus.gmIso S).inv_hom_id
  rw [h, Category.comp_id]

theorem comapIso_proj (R : CommRingCat.{u}) :
    characterLattice.comapIso (T := Gm (Spec R)) (T' := splitTorus.commGroupScheme _ PUnit)
      (splitTorus.gmIso (Spec R)) (splitTorus.proj _ PUnit PUnit.unit) = 𝟙 (Gm (Spec R)) := by
  apply CommGroupScheme.hom_ext_points
  intro U x
  change x ≫ (splitTorus.gmIso (Spec R)).hom.hom.hom ≫
      (CommGroupScheme.groupHom (splitTorus.proj (Spec R) PUnit PUnit.unit)).hom.hom = x ≫ 𝟙 _
  rw [Category.comp_id, ← Category.assoc]
  apply (Gm.pointsEquiv (Spec R) U).injective
  rw [splitTorus.comp_proj]
  exact gmIso_hom_apply (Spec R) U x

end GmIso

section Weights

variable (k : Type u) [Field k]

/-- The character `t ↦ t ^ n` of the rank-one split torus. -/
abbrev rankOneCharacter (n : ℤ) :
    characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) PUnit) :=
  (splitTorus.characterLatticeEquiv k PUnit).symm (fun _ => n)

theorem powerHom_eq_comapIso (n : ℤ) :
    Gm.powerHom (Spec (CommRingCat.of k)) n =
      characterLattice.comapIso (T := Gm _)
        (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) PUnit)
        (splitTorus.gmIso (Spec (CommRingCat.of k))) (rankOneCharacter k n) := by
  rw [rankOneCharacter, splitTorus.characterLatticeEquiv_symm_eq, Fintype.sum_unique,
    map_zsmul]
  change _ = n • characterLattice.comapIso (T := Gm _)
    (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) PUnit) (splitTorus.gmIso _)
    (splitTorus.proj _ PUnit PUnit.unit)
  rw [comapIso_proj, Gm.powerHom_apply]

variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)

/-- The cocharacter, read on the rank-one split torus. -/
abbrev torusHom : splitTorus (Spec (CommRingCat.of k)) PUnit ⟶ G :=
  (splitTorus.gmIso (Spec (CommRingCat.of k))).inv ≫ χ

theorem weightSpace_powerHom (n : ℤ) :
    weightSpace χ (Gm.powerHom (Spec (CommRingCat.of k)) n) =
      weightSpace (torusHom k G χ) (rankOneCharacter k n) := by
  rw [powerHom_eq_comapIso, weightSpace_comapIso]

variable [LocallyOfFiniteType G.X.hom]

/-- The weight coefficients of a Lie vector, indexed by exponents. -/
abbrev weightCoeffs (X : Additive (lieKernel G k)) :
    (PUnit.{u + 1} → ℤ) →₀ Additive (lieKernel G k) :=
  splitTorus.universalAdjointCoefficients PUnit G (torusHom k G χ) X

theorem weightCoeffs_mem (X : Additive (lieKernel G k)) (n : ℤ) :
    weightCoeffs k G χ X (fun _ => n) ∈
      weightSpace χ (Gm.powerHom (Spec (CommRingCat.of k)) n) := by
  rw [weightSpace_powerHom]
  have h := splitTorus.characterAdjointCoefficients_mem k PUnit G (torusHom k G χ) X
    (rankOneCharacter k n)
  rwa [splitTorus.characterAdjointCoefficients_apply, AddEquiv.apply_symm_apply] at h

theorem weightCoeffs_of_mem (X : Additive (lieKernel G k)) (n : ℤ)
    (hX : X ∈ weightSpace χ (Gm.powerHom (Spec (CommRingCat.of k)) n)) :
    weightCoeffs k G χ X = Finsupp.single (fun _ => n) X := by
  rw [weightSpace_powerHom] at hX
  exact splitTorus.universalAdjointCoefficients_of_mem_weightSpace k PUnit G
    (torusHom k G χ) _ X hX

theorem weightCoeffs_sum (X : Additive (lieKernel G k)) :
    (weightCoeffs k G χ X).sum (fun _ y => y) = X :=
  splitTorus.universalAdjointCoefficients_sum PUnit G (torusHom k G χ) X

theorem weightCoeffs_apply_of_mem (X : Additive (lieKernel G k)) (n m : ℤ)
    (hX : X ∈ weightSpace χ (Gm.powerHom (Spec (CommRingCat.of k)) n)) :
    weightCoeffs k G χ X (fun _ => m) = if m = n then X else 0 := by
  rw [weightCoeffs_of_mem k G χ X n hX, Finsupp.single_apply]
  by_cases h : m = n
  · subst h
    simp
  · have h' : ¬((fun _ => n) = fun _ : PUnit.{u + 1} => m) :=
      fun h' => h (congrFun h' PUnit.unit).symm
    simp only [h', h, ↓reduceIte]

/-- Membership in the weight space of the trivial character, read on coefficients. -/
theorem mem_weightSpace_zero_iff (X : Additive (lieKernel G k)) :
    X ∈ weightSpace χ (Gm.powerHom (Spec (CommRingCat.of k)) 0) ↔
      ∀ n : ℤ, weightCoeffs k G χ X (fun _ => n) = if n = 0 then X else 0 := by
  refine ⟨fun hX n => weightCoeffs_apply_of_mem k G χ X 0 n hX, fun h => ?_⟩
  have h0 := h 0
  simp only [↓reduceIte] at h0
  rw [← h0]
  exact weightCoeffs_mem k G χ X 0

set_option maxHeartbeats 2000000 in
/-- Membership in a sum of weight spaces, read on coefficients. -/
theorem mem_iSup_weightSpace_iff (s : ℕ → ℤ) (X : Additive (lieKernel G k)) :
    X ∈ ⨆ j, weightSpace χ (Gm.powerHom (Spec (CommRingCat.of k)) (s j)) ↔
      ∀ n : ℤ, n ∉ Set.range s → weightCoeffs k G χ X (fun _ => n) = 0 := by
  constructor
  · intro hX
    refine Submodule.iSup_induction _
      (motive := fun Y => ∀ n : ℤ, n ∉ Set.range s → weightCoeffs k G χ Y (fun _ => n) = 0)
      hX ?_ ?_ ?_
    · intro j Y hY n hn
      have hne : n ≠ s j := by
        rintro rfl
        exact hn ⟨j, rfl⟩
      rw [weightCoeffs_apply_of_mem k G χ Y (s j) n hY]
      simp only [hne, ↓reduceIte]
    · intro n _
      rw [show weightCoeffs k G χ 0 = 0 from LinearMap.map_zero _]
      rfl
    · intro Y Z hY hZ n hn
      rw [show weightCoeffs k G χ (Y + Z) = weightCoeffs k G χ Y + weightCoeffs k G χ Z from
        LinearMap.map_add _ Y Z, Finsupp.add_apply, hY n hn, hZ n hn, add_zero]
  · intro h
    rw [← weightCoeffs_sum k G χ X]
    have key : ∀ n : ℤ, weightCoeffs k G χ X (fun _ => n) ∈
        ⨆ j, weightSpace χ (Gm.powerHom (Spec (CommRingCat.of k)) (s j)) := by
      intro n
      by_cases hr : n ∈ Set.range s
      · obtain ⟨j, rfl⟩ := hr
        exact Submodule.mem_iSup_of_mem
          (p := fun j => weightSpace χ (Gm.powerHom (Spec (CommRingCat.of k)) (s j))) j
          (weightCoeffs_mem k G χ X (s j))
      · rw [h n hr]
        exact Submodule.zero_mem _
    have key' : ∀ m : PUnit.{u + 1} → ℤ, weightCoeffs k G χ X m ∈
        ⨆ j, weightSpace χ (Gm.powerHom (Spec (CommRingCat.of k)) (s j)) := by
      intro m
      have hm : (fun _ : PUnit.{u + 1} => m PUnit.unit) = m := funext fun x => by cases x; rfl
      have hk := key (m PUnit.unit)
      rw [hm] at hk
      exact hk
    change ∑ m ∈ (weightCoeffs k G χ X).support, weightCoeffs k G χ X m ∈ _
    exact Submodule.sum_mem (⨆ j, weightSpace χ (Gm.powerHom (Spec (CommRingCat.of k)) (s j)))
      fun m _ => key' m

end Weights

section Chart

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]
  [IsAffine G.X.left]

/-- Global sections of `G` mapped to the chosen Lie coordinates. -/
def chartCoordinates : Γ(G.X.left, ⊤) ⟶ CommRingCat.of (Lie.coordinateAlgebra G) :=
  Spec.preimage ((Lie.coordinateIso G).hom.left ≫ G.X.left.isoSpec.hom)

/-- The chosen Lie coordinates mapped to global sections of `G`. -/
def coordinatesChart : CommRingCat.of (Lie.coordinateAlgebra G) ⟶ Γ(G.X.left, ⊤) :=
  Spec.preimage (G.X.left.isoSpec.inv ≫ (Lie.coordinateIso G).inv.left)

theorem coordinatesChart_comp_chartCoordinates :
    coordinatesChart G ≫ chartCoordinates G = 𝟙 _ := by
  apply Spec.map_injective
  rw [Spec.map_comp, chartCoordinates, coordinatesChart, Spec.map_preimage, Spec.map_preimage,
    Spec.map_id, Category.assoc, Iso.hom_inv_id_assoc, ← Over.comp_left, Iso.hom_inv_id]
  rfl

theorem chartCoordinates_surjective : Function.Surjective (chartCoordinates G) := fun c =>
  ⟨coordinatesChart G c, by
    rw [← CommRingCat.comp_apply, coordinatesChart_comp_chartCoordinates]
    rfl⟩

variable {G}

/-- The chart coordinates of an affine point are its Lie coordinates, through the comparison
`chartCoordinates`. -/
theorem pointRing_eq_pointCoordinates {A : Type u} [CommRing A] [Algebra R A]
    (y : Lie.AffinePoints G A) :
    Dynamic.AffineChart.pointRing y =
      chartCoordinates G ≫ CommRingCat.ofHom (Lie.pointCoordinates G y).toRingHom := by
  apply Spec.map_injective
  rw [Dynamic.AffineChart.specMap_pointRing, Spec.map_comp, chartCoordinates, Spec.map_preimage]
  conv_lhs => rw [← (Lie.pointCoordinates G).symm_apply_apply y]
  change (((algSpec R).map (CommAlgCat.ofHom (Lie.pointCoordinates G y)).op ≫
    (Lie.coordinateIso G).hom).left) ≫ _ = _
  rw [Over.comp_left, Category.assoc]
  rfl

end Chart

section Membership

open Dynamic.AffineChart AffineLine

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (χ : (Gm (Spec R)).toGrp ⟶ G) {A : CommRingCat.{u}} {f : Spec A ⟶ Spec R}

/-- A point over `Spec A` lies in `P_G(χ)` exactly when its chart coordinates kill the
coefficients of negative degree of the coaction. -/
theorem chart_mem_parabolic_iff (x : Over.mk f ⟶ G.X) :
    x ∈ (Dynamic.parabolic χ).carrier (Over.mk f) ↔
      ∀ b, ∀ n < 0, pointRing x ((coaction χ b).coeff n) = 0 := by
  constructor
  · rintro ⟨E, hE⟩ b n hn
    have hθ := pointRing_comp_polynomialToLaurent (laurentInclusion_comp_of_whiskerLeft f hE)
    rw [← Corepresented.coeff_laurentCoeffMap, ← CommRingCat.comp_apply, ← hθ,
      CommRingCat.comp_apply]
    exact coeff_toLaurent_of_neg _ hn
  · intro h
    have hL : ∀ b, ∀ n < 0, ((coaction χ ≫ laurentCoeffMap (pointRing x)) b).coeff n = 0 :=
      fun b n hn =>
        (Corepresented.coeff_laurentCoeffMap (pointRing x) (coaction χ b) n).trans (h b n hn)
    exact ⟨polynomialPointInv f ≫ polynomialExtension χ x _ (polynomialLift_comp _ hL),
      whiskerLeft_comp_of_laurentInclusion f (laurentInclusion_comp_polynomialExtension x _ _)⟩

/-- A point over `Spec A` lies in `Z_G(χ)` exactly when the coaction followed by its chart
coordinates is the constant Laurent extension of its chart coordinates. -/
theorem chart_mem_centralizer_iff (x : Over.mk f ⟶ G.X) :
    x ∈ (Dynamic.centralizer χ).carrier (Over.mk f) ↔
      coaction χ ≫ laurentCoeffMap (pointRing x) =
        pointRing x ≫ polynomialC A ≫ polynomialToLaurent A := by
  rw [Dynamic.mem_centralizer]
  have hfst : pointRing (laurentPoint f ≫ fst (Over.mk f) (Gm (Spec R)).X ≫ x) =
      pointRing x ≫ polynomialC A ≫ polynomialToLaurent A := by
    rw [← Category.assoc, pointRing_comp]
    congr 1
    rw [laurentPoint, lift_fst]
    change Spec.preimage (Spec.map (polynomialToLaurent A) ≫ Spec.map (polynomialC A)) = _
    rw [← Spec.map_comp, Spec.preimage_map]
  constructor
  · intro h
    rw [← pointRing_laurentPoint_comp_orbit, h, hfst]
  · intro h
    have h' : laurentPoint f ≫ Dynamic.orbit χ x =
        laurentPoint f ≫ fst (Over.mk f) (Gm (Spec R)).X ≫ x :=
      hom_ext_of_pointRing (by rw [pointRing_laurentPoint_comp_orbit, hfst, h])
    have h'' := congrArg (laurentPointInv f ≫ ·) h'
    simpa only [reassoc_of% (laurentPointInv_comp_laurentPoint f)] using h''

end Membership

section Laurent

variable (k : Type u) [Field k]

theorem const_eq_zero_iff (n : ℤ) : ((fun _ => n : PUnit.{u + 1} → ℤ) = 0) ↔ n = 0 :=
  ⟨fun h => congrFun h PUnit.unit, fun h => by subst h; rfl⟩

/-- Exponent vectors of the rank-one split torus are integers. -/
abbrev exponentEquiv : (PUnit.{u + 1} → ℤ) ≃+ ℤ := AddEquiv.piUnique fun _ => ℤ

/-- The constant part of `laurentPsiAlg`: the monomial of exponent `m` goes to `T ^ m`. -/
def laurentInl : AddMonoidAlgebra k (PUnit.{u + 1} → ℤ) →ₐ[k] LaurentPolynomial (DualNumber k) :=
  (AddMonoidAlgebra.mapAlgHom ℤ (TrivSqZeroExt.inlAlgHom k k k)).comp
    (AddMonoidAlgebra.domCongr k k exponentEquiv.{u}).toAlgHom

theorem coeff_laurentInl (p : AddMonoidAlgebra k (PUnit.{u + 1} → ℤ)) (n : ℤ) :
    (laurentInl k p).coeff n = TrivSqZeroExt.inl (p.coeff fun _ => n) := by
  simp only [laurentInl, AlgHom.comp_apply, AddMonoidAlgebra.coeff_mapAlgHom]
  change TrivSqZeroExt.inlAlgHom k k k
    ((AddMonoidAlgebra.domCongr k k exponentEquiv.{u} p).coeff n) = _
  rw [AddMonoidAlgebra.coeff_domCongr]
  rfl

/-- The infinitesimal part of `laurentPsiAlg`. -/
def laurentInr : AddMonoidAlgebra k (PUnit.{u + 1} → ℤ) →ₗ[k] LaurentPolynomial (DualNumber k) :=
  LinearMap.mulLeft k (LaurentPolynomial.C (TrivSqZeroExt.inr 1 : DualNumber k)) ∘ₗ
    (laurentInl k).toLinearMap

theorem laurentInr_apply (p : AddMonoidAlgebra k (PUnit.{u + 1} → ℤ)) :
    laurentInr k p = LaurentPolynomial.C (TrivSqZeroExt.inr 1 : DualNumber k) * laurentInl k p :=
  rfl

/-- The algebra map `(k[t^{±1}])[ε] → (k[ε])[T^{±1}]`, `t ↦ T`, `ε ↦ ε`. -/
def laurentPsiAlg :
    DualNumber (AddMonoidAlgebra k (PUnit.{u + 1} → ℤ)) →ₐ[k] LaurentPolynomial (DualNumber k) :=
  TrivSqZeroExt.lift (laurentInl k) (laurentInr k)
    (fun x y => by
      rw [laurentInr_apply, laurentInr_apply,
        show ∀ a b c d : LaurentPolynomial (DualNumber k), a * b * (c * d) = a * c * (b * d) from
          fun a b c d => by ring, ← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero, zero_mul])
    (fun r x => by
      rw [laurentInr_apply, laurentInr_apply, smul_eq_mul, map_mul]
      ring)
    (fun r x => by
      rw [laurentInr_apply, laurentInr_apply, op_smul_eq_mul, map_mul]
      ring)

theorem coeff_laurentPsiAlg_fst (z : DualNumber (AddMonoidAlgebra k (PUnit.{u + 1} → ℤ)))
    (n : ℤ) : ((laurentPsiAlg k z).coeff n).fst = z.fst.coeff fun _ => n := by
  rw [laurentPsiAlg, TrivSqZeroExt.lift_def, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    laurentInr_apply, ← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single_zero_mul,
    coeff_laurentInl, coeff_laurentInl]
  simp

theorem coeff_laurentPsiAlg_snd (z : DualNumber (AddMonoidAlgebra k (PUnit.{u + 1} → ℤ)))
    (n : ℤ) : ((laurentPsiAlg k z).coeff n).snd = z.snd.coeff fun _ => n := by
  rw [laurentPsiAlg, TrivSqZeroExt.lift_def, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    laurentInr_apply, ← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single_zero_mul,
    coeff_laurentInl, coeff_laurentInl]
  simp

theorem coeff_algebraMap_torus (a : k) (n : ℤ) :
    (algebraMap k (AddMonoidAlgebra k (PUnit.{u + 1} → ℤ)) a).coeff (fun _ => n) =
      if n = 0 then a else 0 := by
  rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  by_cases h : n = 0
  · subst h
    have h' : (0 : PUnit.{u + 1} → ℤ) = fun _ => 0 := rfl
    simp only [h', ↓reduceIte, Algebra.algebraMap_self, RingHom.id_apply]
  · have h' : ¬((0 : PUnit.{u + 1} → ℤ) = fun _ => n) := fun h' =>
      h ((const_eq_zero_iff n).1 h'.symm)
    simp only [h', h, ↓reduceIte]

/-- The structure morphism of `Spec k[ε]`. -/
abbrev dualMap : Spec (CommRingCat.of (DualNumber k)) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))

/-- The ring map `ψ`. -/
abbrev laurentPsi : CommRingCat.of (DualNumber (AddMonoidAlgebra k (PUnit.{u + 1} → ℤ))) ⟶
    CommRingCat.of (LaurentPolynomial (CommRingCat.of (DualNumber k))) :=
  CommRingCat.ofHom (laurentPsiAlg k).toRingHom

open AffineLine in
/-- `Spec ψ`, as a morphism over `Spec k`. -/
def laurentHom : laurentScheme (dualMap k) ⟶
    (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k)
      (DualNumber (AddMonoidAlgebra (CommRingCat.of k) (PUnit.{u + 1} → ℤ))))) :=
  Over.homMk (Spec.map (laurentPsi k)) (by
    change Spec.map (laurentPsi k) ≫ Spec.map (CommRingCat.ofHom (algebraMap _ _)) =
      Spec.map (polynomialToLaurent _) ≫ Spec.map (polynomialC _) ≫ dualMap k
    rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    change laurentPsiAlg k (algebraMap k _ c) =
      Polynomial.toLaurent (Polynomial.C (algebraMap k (DualNumber k) c))
    rw [AlgHom.commutes, Polynomial.toLaurent_C, LaurentPolynomial.algebraMap_apply])

end Laurent

section Orbit

open AffineLine

variable (k : Type u) [Field k]

/-- On the Laurent test scheme, `Spec ψ` followed by the coefficient change is the first
projection of the Laurent point. -/
theorem laurentHom_comp_coefficient :
    laurentHom k ≫ (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom
      (GeneralLinear.DualNumber.coefficientAlgMap (Algebra.ofId (CommRingCat.of k)
        (AddMonoidAlgebra (CommRingCat.of k) (PUnit.{u + 1} → ℤ))))).op =
      laurentPoint (dualMap k) ≫ fst (Over.mk (dualMap k)) (Gm (Spec (CommRingCat.of k))).X := by
  apply Over.OverMorphism.ext
  rw [laurentPoint, lift_fst]
  change Spec.map (laurentPsi k) ≫ Spec.map (CommRingCat.ofHom
      (GeneralLinear.DualNumber.coefficientAlgMap (Algebra.ofId (CommRingCat.of k)
        (AddMonoidAlgebra (CommRingCat.of k) (PUnit.{u + 1} → ℤ)))).toRingHom) =
    Spec.map (polynomialToLaurent _) ≫ Spec.map (polynomialC _)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change laurentPsiAlg k (GeneralLinear.DualNumber.coefficientAlgMap _ z) =
    Polynomial.toLaurent (Polynomial.C z)
  rw [Polynomial.toLaurent_C]
  apply LaurentPolynomial.ext
  intro n
  rw [LaurentPolynomial.C_apply]
  apply TrivSqZeroExt.ext
  · rw [coeff_laurentPsiAlg_fst]
    change (algebraMap k (AddMonoidAlgebra k (PUnit.{u + 1} → ℤ)) z.fst).coeff _ = _
    rw [coeff_algebraMap_torus]
    split_ifs <;> rfl
  · rw [coeff_laurentPsiAlg_snd]
    change (algebraMap k (AddMonoidAlgebra k (PUnit.{u + 1} → ℤ)) z.snd).coeff _ = _
    rw [coeff_algebraMap_torus]
    split_ifs <;> rfl

theorem pointsEquiv_universalPoint :
    ((splitTorus.pointsEquiv PUnit _ (splitTorus.universalPoint (R := CommRingCat.of k) PUnit))
      PUnit.unit).val =
      (Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra (CommRingCat.of k)
        (PUnit.{u + 1} → ℤ)))).inv
        (AddMonoidAlgebra.single (Pi.single PUnit.unit 1 : PUnit.{u + 1} → ℤ)
          (1 : CommRingCat.of k)) := by
  have h := congrArg (fun t => ((t PUnit.unit : (AddMonoidAlgebra (CommRingCat.of k)
    (PUnit.{u + 1} → ℤ))ˣ) : AddMonoidAlgebra (CommRingCat.of k) (PUnit.{u + 1} → ℤ)))
    (splitTorus.algebraPointsEquiv_universalPoint (R := CommRingCat.of k) PUnit)
  change (Scheme.ΓSpecIso _).hom ((splitTorus.pointsEquiv PUnit _
    (splitTorus.universalPoint (R := CommRingCat.of k) PUnit)) PUnit.unit).val = _ at h
  rw [← Iso.hom_inv_id_apply (Scheme.ΓSpecIso _) ((splitTorus.pointsEquiv PUnit _
    (splitTorus.universalPoint (R := CommRingCat.of k) PUnit)) PUnit.unit).val, h]
  rfl

/-- On the Laurent test scheme, `Spec ψ` followed by the constant universal torus point is the
second projection of the Laurent point. -/
theorem laurentHom_comp_constant :
    laurentHom k ≫ (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom
      (TrivSqZeroExt.inlAlgHom (CommRingCat.of k)
        (AddMonoidAlgebra (CommRingCat.of k) (PUnit.{u + 1} → ℤ))
        (AddMonoidAlgebra (CommRingCat.of k) (PUnit.{u + 1} → ℤ)))).op ≫
      splitTorus.universalPoint PUnit ≫
        (splitTorus.gmIso (Spec (CommRingCat.of k))).inv.hom.hom =
      laurentPoint (dualMap k) ≫ snd (Over.mk (dualMap k)) (Gm (Spec (CommRingCat.of k))).X := by
  apply (Gm.pointsEquiv _ _).injective
  rw [← Category.assoc, ← Category.assoc, gmIso_inv_apply, splitTorus.pointsEquiv_naturality,
    laurentPoint, lift_snd, MulEquiv.apply_symm_apply]
  apply Units.ext
  change (laurentHom k ≫ (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom
      (TrivSqZeroExt.inlAlgHom (CommRingCat.of k)
        (AddMonoidAlgebra (CommRingCat.of k) (PUnit.{u + 1} → ℤ))
        (AddMonoidAlgebra (CommRingCat.of k) (PUnit.{u + 1} → ℤ)))).op).left.appTop
      ((splitTorus.pointsEquiv PUnit _ (splitTorus.universalPoint (R := CommRingCat.of k) PUnit))
        PUnit.unit).val =
    (Scheme.ΓSpecIso _).inv (LaurentPolynomial.T 1)
  rw [pointsEquiv_universalPoint]
  refine (Corepresented.appTop_ΓSpecIso_inv_of_specMap_eq
    (A' := CommRingCat.of (LaurentPolynomial (CommRingCat.of (DualNumber k))))
    (D := CommRingCat.of (AddMonoidAlgebra (CommRingCat.of k) (PUnit.{u + 1} → ℤ)))
    (CommRingCat.ofHom (TrivSqZeroExt.inlAlgHom (CommRingCat.of k)
        (AddMonoidAlgebra (CommRingCat.of k) (PUnit.{u + 1} → ℤ))
        (AddMonoidAlgebra (CommRingCat.of k) (PUnit.{u + 1} → ℤ))).toRingHom ≫ laurentPsi k)
    (laurentHom k ≫ (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom
      (TrivSqZeroExt.inlAlgHom (CommRingCat.of k)
        (AddMonoidAlgebra (CommRingCat.of k) (PUnit.{u + 1} → ℤ))
        (AddMonoidAlgebra (CommRingCat.of k) (PUnit.{u + 1} → ℤ)))).op).left
    (by rw [Spec.map_comp]; rfl) _).trans ?_
  congr 1
  change laurentPsiAlg k (TrivSqZeroExt.inl _) = _
  rw [laurentPsiAlg, TrivSqZeroExt.lift_apply_inl]
  apply LaurentPolynomial.ext
  intro n
  rw [coeff_laurentInl, LaurentPolynomial.T_apply, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  by_cases h : n = 1
  · subst h
    have h' : (Pi.single PUnit.unit 1 : PUnit.{u + 1} → ℤ) = fun _ => 1 := by
      funext x
      rfl
    simp only [h', ↓reduceIte]
    rfl
  · have h' : ¬((Pi.single PUnit.unit 1 : PUnit.{u + 1} → ℤ) = fun _ => n) := fun h' =>
      h (by simpa using (congrFun h' PUnit.unit).symm)
    simp only [h', Ne.symm h, ↓reduceIte, TrivSqZeroExt.inl_zero]

end Orbit

section Identity

open AffineLine

attribute [local instance] Lie.coordinateOriginAlgebra

variable (k : Type u) [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)

/-- A Lie vector, as a point of `G` over `Spec k[ε]` with its structure morphism `dualMap k`. -/
def dualPoint (X : lieKernel G k) : Over.mk (dualMap k) ⟶ G.X :=
  X.val

/-- The universal adjoint vector `Ad(χ(t)) X` over `k[t^{±1}]`. -/
abbrev universalVector (X : lieKernel G k) :
    lieKernel G (AddMonoidAlgebra (CommRingCat.of k) (PUnit.{u + 1} → ℤ)) :=
  (splitTorus.universalAdjoint PUnit G (torusHom k G χ) (Additive.ofMul X)).toMul

/-- The orbit map of a Lie vector on `Spec (k[ε])[T^{±1}]` is the universal adjoint vector,
pulled back along `Spec ψ`. -/
theorem laurentPoint_comp_orbit_eq (X : lieKernel G k) :
    laurentPoint (dualMap k) ≫ Dynamic.orbit χ (dualPoint k X) =
      laurentHom k ≫ (universalVector k χ X).val := by
  have hc : laurentHom k ≫
      Lie.constant G (splitTorus.universalPoint PUnit ≫ (torusHom k G χ).hom.hom) =
        laurentPoint (dualMap k) ≫ snd (Over.mk (dualMap k)) (Gm (Spec (CommRingCat.of k))).X ≫
          χ.hom.hom := by
    rw [← reassoc_of% (laurentHom_comp_constant k)]
    rfl
  have hx : laurentHom k ≫ Lie.affineMap G (GeneralLinear.DualNumber.coefficientAlgMap
      (Algebra.ofId (CommRingCat.of k)
        (AddMonoidAlgebra (CommRingCat.of k) (PUnit.{u + 1} → ℤ)))) X.val =
        laurentPoint (dualMap k) ≫ fst (Over.mk (dualMap k)) (Gm (Spec (CommRingCat.of k))).X ≫
          dualPoint k X := by
    rw [← reassoc_of% (laurentHom_comp_coefficient k)]
    rfl
  change _ = laurentHom k ≫
    (Lie.constant G (splitTorus.universalPoint PUnit ≫ (torusHom k G χ).hom.hom) *
      Lie.affineMap G (GeneralLinear.DualNumber.coefficientAlgMap
        (Algebra.ofId (CommRingCat.of k)
          (AddMonoidAlgebra (CommRingCat.of k) (PUnit.{u + 1} → ℤ)))) X.val *
      (Lie.constant G (splitTorus.universalPoint PUnit ≫ (torusHom k G χ).hom.hom))⁻¹)
  rw [Dynamic.orbit]
  simp only [MonObj.comp_mul, GrpObj.comp_inv]
  rw [hc, hx]

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

omit [LocallyOfFiniteType G.X.hom] in
/-- The chart coordinates of the orbit coaction of a Lie vector. -/
theorem coaction_comp_laurentCoeffMap (X : lieKernel G k) :
    Dynamic.AffineChart.coaction χ ≫
      laurentCoeffMap (Dynamic.AffineChart.pointRing (dualPoint k X)) =
      chartCoordinates G ≫ CommRingCat.ofHom
        (Lie.pointCoordinates G (universalVector k χ X).val).toRingHom ≫ laurentPsi k := by
  rw [← Dynamic.AffineChart.pointRing_laurentPoint_comp_orbit, laurentPoint_comp_orbit_eq,
    Dynamic.AffineChart.pointRing_comp]
  rw [show Dynamic.AffineChart.pointRing (universalVector k χ X).val =
    chartCoordinates G ≫ CommRingCat.ofHom (Lie.pointCoordinates G (universalVector k χ X).val).toRingHom
    from pointRing_eq_pointCoordinates _, Category.assoc]
  congr 2
  exact Spec.preimage_map _

omit [LocallyOfFiniteType G.X.hom] in
theorem pointRing_coaction_coeff (X : lieKernel G k) (b : Γ(G.X.left, ⊤)) (n : ℤ) :
    Dynamic.AffineChart.pointRing (dualPoint k X)
        ((Dynamic.AffineChart.coaction χ b).coeff n) =
      (laurentPsiAlg k (Lie.pointCoordinates G (universalVector k χ X).val
        (chartCoordinates G b))).coeff n := by
  have h := congrArg (fun φ => (φ b).coeff n) (coaction_comp_laurentCoeffMap k χ X)
  simp only at h
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, CommRingCat.comp_apply,
    Corepresented.coeff_laurentCoeffMap] at h
  exact h

omit [LocallyOfFiniteType G.X.hom] in
theorem pointRing_coaction_coeff_fst (X : lieKernel G k) (b : Γ(G.X.left, ⊤)) (n : ℤ) :
    (Dynamic.AffineChart.pointRing (dualPoint k X)
        ((Dynamic.AffineChart.coaction χ b).coeff n)).fst =
      if n = 0 then Lie.coordinateOrigin G (chartCoordinates G b) else 0 := by
  rw [pointRing_coaction_coeff, coeff_laurentPsiAlg_fst]
  have hk := congrArg (fun φ => φ (chartCoordinates G b))
    (Lie.pointCoordinates_kernel G (universalVector k χ X))
  change ((TrivSqZeroExt.fstHom _ _ _).comp
    (Lie.pointCoordinates G (universalVector k χ X).val) (chartCoordinates G b)).coeff _ = _
  rw [show ((TrivSqZeroExt.fstHom _ _ _).comp
    (Lie.pointCoordinates G (universalVector k χ X).val) (chartCoordinates G b)) = _ from hk]
  change (algebraMap k (AddMonoidAlgebra k (PUnit.{u + 1} → ℤ))
    (Lie.coordinateOrigin G (chartCoordinates G b))).coeff _ = _
  rw [coeff_algebraMap_torus]

theorem pointRing_coaction_coeff_snd (X : lieKernel G k) (b : Γ(G.X.left, ⊤)) (n : ℤ) :
    (Dynamic.AffineChart.pointRing (dualPoint k X)
        ((Dynamic.AffineChart.coaction χ b).coeff n)).snd =
      Lie.kernelDerivationLinearEquiv G
        (weightCoeffs k G χ (Additive.ofMul X) (fun _ => n)) (chartCoordinates G b) := by
  rw [pointRing_coaction_coeff, coeff_laurentPsiAlg_snd, weightCoeffs,
    splitTorus.universalAdjointCoefficients_apply, Lie.kernelCoefficient_apply]
  rfl

end Identity

section Assembly

open AffineLine

attribute [local instance] Lie.coordinateOriginAlgebra

variable (k : Type u) [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)

omit [LocallyOfFiniteType G.X.hom] in
/-- Lie vectors are determined by their derivations on chart coordinates. -/
theorem eq_of_chart {Y Z : Additive (lieKernel G k)}
    (h : ∀ b, Lie.kernelDerivationLinearEquiv G Y (chartCoordinates G b) =
      Lie.kernelDerivationLinearEquiv G Z (chartCoordinates G b)) : Y = Z := by
  apply (Lie.kernelDerivationLinearEquiv G).injective
  apply Derivation.ext
  intro c
  obtain ⟨b, rfl⟩ := chartCoordinates_surjective G c
  exact h b

omit [LocallyOfFiniteType G.X.hom] in
theorem pointRing_dualPoint (X : lieKernel G k) (b : Γ(G.X.left, ⊤)) :
    Dynamic.AffineChart.pointRing (dualPoint k X) b =
      Lie.pointCoordinates G X.val (chartCoordinates G b) := by
  rw [show Dynamic.AffineChart.pointRing (dualPoint k X) = chartCoordinates G ≫
    CommRingCat.ofHom (Lie.pointCoordinates G X.val).toRingHom from
      pointRing_eq_pointCoordinates X.val]
  rfl

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem pointCoordinates_fst (X : lieKernel G k) (c : Lie.coordinateAlgebra G) :
    (Lie.pointCoordinates G X.val c).fst = Lie.coordinateOrigin G c := by
  have h := congrArg (fun φ => φ c) (Lie.pointCoordinates_kernel G X)
  simpa using h

omit [LocallyOfFiniteType G.X.hom] in
theorem counit_eq (b : Γ(G.X.left, ⊤)) :
    Dynamic.AffineChart.counit G b = Lie.coordinateOrigin G (chartCoordinates G b) := by
  have h1 := Dynamic.AffineChart.pointRing_one (G := G) (f := dualMap k)
  have h2 : Dynamic.AffineChart.pointRing (1 : Over.mk (dualMap k) ⟶ G.X) =
      chartCoordinates G ≫ CommRingCat.ofHom
        (Lie.pointCoordinates G (1 : Lie.AffinePoints G (DualNumber k))).toRingHom :=
    pointRing_eq_pointCoordinates (1 : Lie.AffinePoints G (DualNumber k))
  rw [h1, Lie.pointCoordinates_one, Spec.preimage_map] at h2
  have h3 := congrArg (fun φ => (φ b).fst) h2
  simpa [TrivSqZeroExt.algebraMap_eq_inl] using h3

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
theorem coaction_comp_apply_coeff (x : Over.mk (dualMap k) ⟶ G.X) (b : Γ(G.X.left, ⊤))
    (n : ℤ) :
    ((Dynamic.AffineChart.coaction χ ≫ laurentCoeffMap (Dynamic.AffineChart.pointRing x)) b).coeff
        n = Dynamic.AffineChart.pointRing x ((Dynamic.AffineChart.coaction χ b).coeff n) := by
  rw [CommRingCat.comp_apply, Corepresented.coeff_laurentCoeffMap]

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
theorem const_comp_apply_coeff (x : Over.mk (dualMap k) ⟶ G.X) (b : Γ(G.X.left, ⊤)) (n : ℤ) :
    ((Dynamic.AffineChart.pointRing x ≫ polynomialC _ ≫ polynomialToLaurent _) b).coeff n =
      if n = 0 then Dynamic.AffineChart.pointRing x b else 0 := by
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply]
  change (Polynomial.toLaurent (Polynomial.C _)).coeff n = _
  rw [Polynomial.toLaurent_C, LaurentPolynomial.C_apply]

/-- The centralizer clause, read on weight coefficients. -/
theorem mem_centralizer_iff_weightCoeffs (X : lieKernel G k) :
    X.val ∈ (Dynamic.centralizer χ).carrier _ ↔
      ∀ n : ℤ, weightCoeffs k G χ (Additive.ofMul X) (fun _ => n) =
        if n = 0 then Additive.ofMul X else 0 := by
  refine (chart_mem_centralizer_iff χ (dualPoint k X)).trans ⟨fun h n => ?_, fun h => ?_⟩
  · apply eq_of_chart k
    intro b
    have hb := congrArg (fun φ => ((φ b).coeff n).snd) h
    simp only at hb
    rw [coaction_comp_apply_coeff, const_comp_apply_coeff, pointRing_coaction_coeff_snd] at hb
    rw [hb]
    split_ifs
    · rw [pointRing_dualPoint]
      rfl
    · simp
  · refine CommRingCat.hom_ext (RingHom.ext fun b => LaurentPolynomial.ext fun n => ?_)
    show ((Dynamic.AffineChart.coaction χ ≫
        laurentCoeffMap (Dynamic.AffineChart.pointRing (dualPoint k X))) b).coeff n =
      ((Dynamic.AffineChart.pointRing (dualPoint k X) ≫ polynomialC _ ≫
        polynomialToLaurent _) b).coeff n
    rw [coaction_comp_apply_coeff, const_comp_apply_coeff]
    apply TrivSqZeroExt.ext
    · rw [pointRing_coaction_coeff_fst]
      split_ifs
      · rw [pointRing_dualPoint, pointCoordinates_fst]
      · rfl
    · rw [pointRing_coaction_coeff_snd, h n]
      split_ifs
      · rw [pointRing_dualPoint]
        rfl
      · simp

/-- The parabolic clause, read on weight coefficients. -/
theorem mem_parabolic_iff_weightCoeffs (X : lieKernel G k) :
    X.val ∈ (Dynamic.parabolic χ).carrier _ ↔
      ∀ n : ℤ, n < 0 → weightCoeffs k G χ (Additive.ofMul X) (fun _ => n) = 0 := by
  refine (chart_mem_parabolic_iff χ (dualPoint k X)).trans
    ⟨fun h n hn => ?_, fun h b n hn => ?_⟩
  · apply eq_of_chart k
    intro b
    rw [← pointRing_coaction_coeff_snd, h b n hn]
    simp
  · apply TrivSqZeroExt.ext
    · rw [pointRing_coaction_coeff_fst]
      simp [hn.ne]
    · rw [pointRing_coaction_coeff_snd, h n hn]
      simp

/-- The unipotent clause, read on weight coefficients. -/
theorem mem_unipotent_iff_weightCoeffs (X : lieKernel G k) :
    X.val ∈ (Dynamic.unipotent χ).carrier _ ↔
      ∀ n : ℤ, n ≤ 0 → weightCoeffs k G χ (Additive.ofMul X) (fun _ => n) = 0 := by
  have hpre : Spec.preimage (dualMap k) = CommRingCat.ofHom (algebraMap k (DualNumber k)) :=
    Spec.preimage_map _
  refine (Dynamic.AffineChart.mem_unipotent_iff χ (dualPoint k X)).trans
    ⟨fun ⟨hP, h0⟩ n hn => ?_, fun h => ⟨fun b n hn => ?_, fun b => ?_⟩⟩
  · apply eq_of_chart k
    intro b
    rw [← pointRing_coaction_coeff_snd]
    rcases hn.lt_or_eq with hn | rfl
    · rw [hP b n hn]
      simp
    · rw [h0 b, hpre]
      simp [TrivSqZeroExt.algebraMap_eq_inl]
  · apply TrivSqZeroExt.ext
    · rw [pointRing_coaction_coeff_fst]
      simp [hn.ne]
    · rw [pointRing_coaction_coeff_snd, h n hn.le]
      simp
  · apply TrivSqZeroExt.ext
    · rw [pointRing_coaction_coeff_fst, hpre, counit_eq]
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    · rw [pointRing_coaction_coeff_snd, h 0 le_rfl, hpre]
      simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem not_mem_range_natCast_iff (n : ℤ) :
    n ∉ Set.range (fun j : ℕ => (j : ℤ)) ↔ n < 0 := by
  constructor
  · intro h
    by_contra h'
    exact h ⟨n.toNat, Int.toNat_of_nonneg (not_lt.mp h')⟩
  · rintro h ⟨j, hj⟩
    simp only at hj
    omega

theorem not_mem_range_natCast_add_one_iff (n : ℤ) :
    n ∉ Set.range (fun j : ℕ => (j : ℤ) + 1) ↔ n ≤ 0 := by
  constructor
  · intro h
    by_contra h'
    have hn : 0 ≤ n - 1 := by omega
    exact h ⟨(n - 1).toNat, by
      show ((n - 1).toNat : ℤ) + 1 = n
      rw [Int.toNat_of_nonneg hn]
      omega⟩
  · rintro h ⟨j, hj⟩
    simp only at hj
    omega

end Assembly

end Langlands.GroupScheme.DynamicLie

namespace Langlands.GroupScheme

open DynamicLie

/-- **Lie algebras of dynamic subgroups** (Conrad–Gabber–Prasad, Proposition 2.1.8(1)). -/
theorem dynamicLie : DynamicLieStatement.{u} := by
  intro k _ G _ _ χ X
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  refine ⟨(mem_centralizer_iff_weightCoeffs k χ X).trans
    (mem_weightSpace_zero_iff k G χ (Additive.ofMul X)).symm, ?_, ?_⟩
  · refine (mem_parabolic_iff_weightCoeffs k χ X).trans (Iff.trans ?_
      (mem_iSup_weightSpace_iff k G χ (fun j : ℕ => (j : ℤ)) (Additive.ofMul X)).symm)
    exact ⟨fun h n hn => h n ((not_mem_range_natCast_iff n).1 hn),
      fun h n hn => h n ((not_mem_range_natCast_iff n).2 hn)⟩
  · refine (mem_unipotent_iff_weightCoeffs k χ X).trans (Iff.trans ?_
      (mem_iSup_weightSpace_iff k G χ (fun j : ℕ => (j : ℤ) + 1) (Additive.ofMul X)).symm)
    exact ⟨fun h n hn => h n ((not_mem_range_natCast_add_one_iff n).1 hn),
      fun h n hn => h n ((not_mem_range_natCast_add_one_iff n).2 hn)⟩

end Langlands.GroupScheme
