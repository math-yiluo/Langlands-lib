import Langlands.Geometry.Building.Kottwitz.InducedTorusRationalSurjectivityStatement
import Langlands.Geometry.Building.Kottwitz.InducedTorusUniformizerFamily
import Langlands.Geometry.Building.Kottwitz.TorusMapDescentProof
import Langlands.Geometry.Building.Kottwitz.TorusGaloisSplitting

/-! # Proof of KP Corollary 11.1.9: surjectivity for induced tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building.Kottwitz

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- A finite Galois extension of `K` inside `F^sep` containing a given finite Galois
splitting field `E` of `T`; it also splits `T`. -/
theorem exists_galois_splitting_containing (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (E : IntermediateField F (SeparableClosure F)) [FiniteDimensional F E] [IsGalois F E]
    (hE : IsSplitTorus (baseChanged F E T.toGrp)) :
    ∃ L : IntermediateField (UnramifiedClosure F) (SeparableClosure F),
      FiniteDimensional (UnramifiedClosure F) L ∧ IsGalois (UnramifiedClosure F) L ∧
      (∀ x ∈ E, x ∈ L) ∧ IsSplitTorus (baseChanged F L T.toGrp) := by
  obtain ⟨a, ha⟩ := Field.exists_primitive_element F E
  have ha' : IntermediateField.adjoin F {(a : SeparableClosure F)} = E := by
    have h := congrArg (fun N : IntermediateField F E => N.map E.val) ha
    change IntermediateField.adjoin F {E.val a} = E
    simpa only [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val] using h
  let L := IntermediateField.adjoin (UnramifiedClosure F) {(a : SeparableClosure F)}
  have hL : L.restrictScalars F = Langlands.LocalGalois.Separable.inertiaFixedField F ⊔ E := by
    change (IntermediateField.adjoin (Langlands.LocalGalois.Separable.inertiaFixedField F)
      {(a : SeparableClosure F)}).restrictScalars F = _
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, ha']
  let : FiniteDimensional (UnramifiedClosure F) L :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral (R := UnramifiedClosure F) (a : SeparableClosure F))
  let : Normal F L := by
    change Normal F (L.restrictScalars F)
    rw [hL]
    infer_instance
  let : Normal (UnramifiedClosure F) L := Normal.tower_top_of_normal F (UnramifiedClosure F) L
  let : IsGalois (UnramifiedClosure F) L := ⟨⟩
  have hML : E ≤ L.restrictScalars F := hL ▸ le_sup_right
  let i : E →ₐ[F] L := IntermediateField.inclusion hML
  let alg : Algebra E L := i.toRingHom.toAlgebra
  let : SMul E L := alg.toSMul
  let : Algebra E L := alg
  let : IsScalarTower F E L :=
    IsScalarTower.of_algebraMap_eq (R := F) (S := E) (A := L) fun _ => rfl
  exact ⟨L, inferInstance, inferInstance, fun x hx => hML hx,
    IsSplitTorus.baseChange_fieldTower F E L T.toGrp hE⟩

section Core

variable (T : CommGroupScheme (Spec (CommRingCat.of F))) (hT : IsTorus T.toGrp)
  [IsAffine T.X.left]
  (E : IntermediateField F (SeparableClosure F)) [FiniteDimensional F E] [IsGalois F E]
  (hE : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap F E)).obj T).toGrp)
  {J : Type u} [Fintype J] [DecidableEq J]
  (b : Module.Basis J ℤ
    (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F E)).obj T)))
  (hb : ∀ (σ : E ≃ₐ[F] E) (i : J), ∃ j,
    characterLattice.galoisRepresentation F E T σ (b i) = b j)
  [MulAction (SeparableClosure F ≃ₐ[F] SeparableClosure F) J]
  (hact : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (j : J),
    σ • j = InducedCocharacterBasis.indexHom T b hb (σ.restrictNormal E) j)

include hact in
omit [FiniteDimensional F E] in
/-- The orbit sums of a representative of a residually invariant class are Galois invariant. -/
theorem orbitSum_galois_invariant (c : Multiplicative (TorusInvariantTarget F T))
    (ν : geometricCocharacters F (SeparableClosure F) T)
    (hν : inertiaProjection F (UnramifiedClosure F) (SeparableClosure F)
      (cocharacterLattice.galoisRepresentation F (SeparableClosure F) T) ν =
        (c.toAdd : TorusTarget F F T))
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (j : J) :
    PermutationCoinvariants.orbitSum (InducedCocharacterBasis.geometricBasis F E T hE b)
        (relativeInertia F (UnramifiedClosure F) (SeparableClosure F)) ν (σ • j) =
      PermutationCoinvariants.orbitSum (InducedCocharacterBasis.geometricBasis F E T hE b)
        (relativeInertia F (UnramifiedClosure F) (SeparableClosure F)) ν j := by
  have hmk : inertiaProjection F (UnramifiedClosure F) (SeparableClosure F)
        (cocharacterLattice.galoisRepresentation F (SeparableClosure F) T)
        (cocharacterLattice.galoisRepresentation F (SeparableClosure F) T σ⁻¹ ν) =
      inertiaProjection F (UnramifiedClosure F) (SeparableClosure F)
        (cocharacterLattice.galoisRepresentation F (SeparableClosure F) T) ν := by
    have hinv := (Representation.mem_invariants _ _).mp c.toAdd.2
      (σ⁻¹.restrictNormal (UnramifiedClosure F))
    rw [← inertiaGammaRepresentation_restrict, hν]
    exact hinv
  have h := PermutationCoinvariants.orbitSum_smul_of_mk_eq
    (cocharacterLattice.galoisRepresentation F (SeparableClosure F) T)
    (InducedCocharacterBasis.geometricBasis F E T hE b)
    (relativeInertia F (UnramifiedClosure F) (SeparableClosure F))
    (InducedCocharacterBasis.galoisRepresentation_geometricBasis_smul F E T hE b hb hact) ν σ⁻¹ hmk j
  rw [inv_inv] at h
  exact h

include hact in
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffine T.X.left] [FiniteDimensional F E] [Fintype J] [DecidableEq J] in
/-- Integral powers of an equivariant family by Galois invariant exponents stay equivariant. -/
theorem zpow_family_equivariant (u : J → Eˣ)
    (hu : ∀ (τ : E ≃ₐ[F] E) (j : J),
      u (InducedCocharacterBasis.indexHom T b hb τ j) = Units.map τ.toMonoidHom (u j))
    (n : J → ℤ) (hn : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (j : J),
      n (σ • j) = n j) (τ : E ≃ₐ[F] E) (j : J) :
    u (InducedCocharacterBasis.indexHom T b hb τ j) ^
        n (InducedCocharacterBasis.indexHom T b hb τ j) =
      Units.map τ.toMonoidHom (u j ^ n j) := by
  have hnE : n (InducedCocharacterBasis.indexHom T b hb τ j) = n j := by
    obtain ⟨σ, hσ⟩ :=
      AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := E) (E := SeparableClosure F) τ
    have h1 := hn σ j
    rw [hact] at h1
    rw [← hσ]
    exact h1
  rw [hu, hnE, map_zpow]

variable (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
  [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
  (hEL : ∀ x ∈ E, x ∈ L)

variable (hL : IsSplitTorus ((CommGroupScheme.baseChange (baseMap F L)).obj T).toGrp)

include hE hb hact hEL hL in
/-- Surjectivity from a permuted character basis over a finite Galois splitting field `E`
and a finite Galois extension `L ⊇ E` of `K`. -/
theorem torusKottwitzRational_surjective_of_basis :
    Function.Surjective (torusKottwitzRational F T hT) := by
  intro c
  obtain ⟨ν, hν⟩ := Representation.Coinvariants.mk_surjective
    ((cocharacterLattice.galoisRepresentation F (SeparableClosure F) T).comp
      (relativeInertia F (UnramifiedClosure F) (SeparableClosure F)).subtype)
    (c.toAdd : TorusTarget F F T)
  have hn := orbitSum_galois_invariant F T E hE b hb hact c ν hν
  obtain ⟨u, hu, hsum⟩ := UniformizerFamily.exists_family F E
    (InducedCocharacterBasis.indexHom T b hb) hact L hEL
  obtain ⟨t, ht⟩ := InducedCocharacterBasis.exists_rationalPoint F E T hE b hb
    (fun j => u j ^ PermutationCoinvariants.orbitSum
      (InducedCocharacterBasis.geometricBasis F E T hE b)
      (relativeInertia F (UnramifiedClosure F) (SeparableClosure F)) ν j)
    (zpow_family_equivariant F T E b hb hact u hu _ hn)
  have hfin := InducedCocharacterBasis.torusKottwitz_eq_of_family F E T hE b L hL hEL hb hact
    hT u hsum ν hn (rationalCoeffEquiv F T.toGrp t) ht
  refine ⟨t, ?_⟩
  have hres := congrArg Multiplicative.toAdd ((torusKottwitzDescent F T hT).2.2 t)
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact hres.trans (hfin.trans hν)

end Core

/-- KP Corollary 11.1.9: the rational Kottwitz map of an induced torus is surjective. -/
theorem inducedTorusKottwitzRationalSurjectivity :
    InducedTorusKottwitzRationalSurjectivityStatement.{u} := by
  intro F _ _ _ _ T hT
  classical
  let : IsAffine T.X.left := torusIsAffine F T hT.isTorus
  obtain ⟨E, hEfin, hEgal, hE⟩ :=
    exists_finiteGaloisSplittingField_inside (SeparableClosure F) T.toGrp hT.isTorus
  let : FiniteDimensional F E := hEfin
  let : IsGalois F E := hEgal
  obtain ⟨J, hJ, b, hb⟩ := hT.exists_permuted_basis E hE
  let : Fintype J := Fintype.ofFinite J
  obtain ⟨L, hLfin, hLgal, hEL, hL⟩ := exists_galois_splitting_containing F T E hE
  let : FiniteDimensional (UnramifiedClosure F) L := hLfin
  let : IsGalois (UnramifiedClosure F) L := hLgal
  let : MulAction (SeparableClosure F ≃ₐ[F] SeparableClosure F) J :=
    MulAction.compHom J (InducedCocharacterBasis.galoisIndexHom F E T b hb)
  exact torusKottwitzRational_surjective_of_basis F T hT.isTorus E hE b hb (fun _ _ => rfl)
    L hEL hL

end Langlands.Geometry.Building.Kottwitz
