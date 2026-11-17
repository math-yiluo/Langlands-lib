import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeTorsion
import Langlands.GroupScheme.Torus.TorsionOrderComparison
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable
import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeTorsionDeterminationStatement
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Clopen torsion comparison, conditional on torsion determination -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.FibralClopen

open Langlands.AlgebraicGeometry.FiniteEtale

/-- Over a separably closed field, field-level multiplicative type supplies
relative multiplicative type through the actual diagonalizable model. -/
theorem relative_of_field_of_isSepClosed {k : Type u} [Field k] [IsSepClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsMultiplicativeType G) :
    RelativeMultiplicativeType.IsMultiplicativeType G := by
  obtain ⟨M, hM, hfg, ⟨e⟩⟩ :=
    MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed G hG
  exact RelativeMultiplicativeType.IsMultiplicativeType.of_iso e
    (RelativeMultiplicativeType.IsMultiplicativeType.of_isDiagonalizable
      (Diagonalizable.isDiagonalizable_groupScheme (CommRingCat.of k) M))

variable
  (hDetermination : MultiplicativeTypeTorsionDeterminationStatement.{u})
  {S : Scheme.{u}} {G H : GroupScheme S} [IsCommMonObj G.X] [IsCommMonObj H.X]
  (j : G ⟶ H) [hOpen : IsOpenImmersion j.hom.hom.left]
  [hClosed : IsClosedImmersion j.hom.hom.left]
  (hG : RelativeMultiplicativeType.IsMultiplicativeType G)
  (hH : ∀ s : S, IsMultiplicativeType (geometricFiber H s))

include hDetermination j hOpen hClosed hG hH

omit hOpen in
/-- Equality of all geometric torsion orders makes each geometric-fibre
embedding invertible, using the supplied torsion-determination theorem. -/
theorem isIso_geometricFiber_of_equalTorsionOrders
    (hOrder : ∀ (n : ℕ), 0 < n → ∀ s : S,
      letI := coordinateAlgebra (torsion (geometricFiber G s) (n : ℤ)).X.hom
      letI := coordinateAlgebra (torsion (geometricFiber H s) (n : ℤ)).X.hom
      Module.finrank (AlgebraicClosure (S.residueField s))
          Γ((torsion (geometricFiber G s) (n : ℤ)).X.left, ⊤) =
        Module.finrank (AlgebraicClosure (S.residueField s))
          Γ((torsion (geometricFiber H s) (n : ℤ)).X.left, ⊤))
    (s : S) : IsIso ((GroupScheme.baseChange (geometricPoint S s)).map j) := by
  let b := geometricPoint S s
  let Gs := geometricFiber G s
  let Hs := geometricFiber H s
  let js := (GroupScheme.baseChange b).map j
  have hGs : RelativeMultiplicativeType.IsMultiplicativeType Gs := hG.baseChange b
  have hHs : RelativeMultiplicativeType.IsMultiplicativeType Hs :=
    relative_of_field_of_isSepClosed Hs (hH s)
  have : IsAffineHom Hs.X.hom := (hH s).isAffineHom
  have : IsClosedImmersion js.hom.hom.left :=
    MorphismProperty.of_isPullback (baseChange_map_isPullback b j).flip inferInstance
  have : IsSeparated Gs.X.hom := by
    rw [← Over.w js.hom.hom]
    infer_instance
  apply (hDetermination _).2.2 Hs Gs js hHs inferInstance
  intro n hn T x hx
  obtain ⟨hfinG, -, -⟩ := hGs.torsion_geometry n hn
  obtain ⟨hfinH, -, -⟩ := hHs.torsion_geometry n hn
  let := hfinG
  let := hfinH
  let E := TorsionOrderComparison.torsionIsoOfFinrankEq js (n : ℤ) (hOrder n hn s)
  let y : T ⟶ (torsion Hs (n : ℤ)).X :=
    (torsionPointsEquiv Hs (n : ℤ) T).symm
      ⟨x, (mem_torsionPoints Hs (n : ℤ) T x).mpr (by simpa only [zpow_natCast] using hx)⟩
  have hy : y ≫ (torsionι Hs (n : ℤ)).hom.hom = x :=
    congrArg Subtype.val ((torsionPointsEquiv Hs (n : ℤ) T).apply_symm_apply _)
  let z := (isoPointsEquiv E T).symm y
  refine ⟨z ≫ (torsionι Gs (n : ℤ)).hom.hom, ?_⟩
  change (z ≫ (torsionι Gs (n : ℤ)).hom.hom) ≫ js.hom.hom = x
  have hι := congrArg (fun f => f.hom.hom) (torsionMap_ι js (n : ℤ))
  change (torsionMap js (n : ℤ)).hom.hom ≫ (torsionι Hs (n : ℤ)).hom.hom =
    (torsionι Gs (n : ℤ)).hom.hom ≫ js.hom.hom at hι
  rw [Category.assoc, ← hι, ← Category.assoc]
  change (isoPointsEquiv E T z) ≫ (torsionι Hs (n : ℤ)).hom.hom = x
  rw [MulEquiv.apply_symm_apply]
  exact hy

/-- A clopen subgroup with multiplicative-type geometric target fibres and
equal torsion orders is the entire target, conditional on torsion determination. -/
def isoOfEqualGeometricTorsionOrders
    (hOrder : ∀ (n : ℕ), 0 < n → ∀ s : S,
      letI := coordinateAlgebra (torsion (geometricFiber G s) (n : ℤ)).X.hom
      letI := coordinateAlgebra (torsion (geometricFiber H s) (n : ℤ)).X.hom
      Module.finrank (AlgebraicClosure (S.residueField s))
          Γ((torsion (geometricFiber G s) (n : ℤ)).X.left, ⊤) =
        Module.finrank (AlgebraicClosure (S.residueField s))
          Γ((torsion (geometricFiber H s) (n : ℤ)).X.left, ⊤)) : G ≅ H := by
  have hgeo := isIso_geometricFiber_of_equalTorsionOrders hDetermination j hG hH hOrder
  have : Surjective j.hom.hom.left := by
    constructor
    intro y
    let s := H.X.hom y
    let b := geometricPoint S s
    let x := IsLocalRing.closedPoint (AlgebraicClosure (S.residueField s))
    have hb : b x = s := by
      change S.fromSpecResidueField s _ = s
      exact Scheme.fromSpecResidueField_apply _ _
    obtain ⟨y', hy', -⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := H.X.hom) (g := b) y x hb.symm
    have : IsIso ((GroupScheme.baseChange b).map j) := hgeo s
    have : IsIso ((GroupScheme.baseChange b).map j).hom.hom.left :=
      (Grp.forget _ ⋙ Over.forget _).map_isIso ((GroupScheme.baseChange b).map j)
    have hsurj : Surjective ((GroupScheme.baseChange b).map j).hom.hom.left := inferInstance
    obtain ⟨z, hz⟩ := hsurj.surj y'
    refine ⟨pullback.fst G.X.hom b z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← (baseChange_map_isPullback b j).w,
      Scheme.Hom.comp_apply]
    exact (congrArg (fun t => (pullback.fst H.X.hom b) t) hz).trans hy'
  have : IsIso j.hom.hom.left := Flat.isIso_of_surjective_of_mono _
  let := TorusIsomorphismLocus.isIso_of_underlying j
  exact asIso j

/-- On a preconnected base, local constancy of target torsion orders and
equality with the subgroup at one point suffice for the same comparison. -/
def isoOfLocallyConstantTorsionOrders [PreconnectedSpace S] (s₀ : S)
    (hOrder : ∀ (n : ℕ), 0 < n → IsLocallyConstant fun s : S =>
      letI := coordinateAlgebra (torsion (geometricFiber H s) (n : ℤ)).X.hom
      Module.finrank (AlgebraicClosure (S.residueField s))
        Γ((torsion (geometricFiber H s) (n : ℤ)).X.left, ⊤))
    (h₀ : ∀ (n : ℕ), 0 < n →
      letI := coordinateAlgebra (torsion (geometricFiber G s₀) (n : ℤ)).X.hom
      letI := coordinateAlgebra (torsion (geometricFiber H s₀) (n : ℤ)).X.hom
      Module.finrank (AlgebraicClosure (S.residueField s₀))
          Γ((torsion (geometricFiber G s₀) (n : ℤ)).X.left, ⊤) =
        Module.finrank (AlgebraicClosure (S.residueField s₀))
          Γ((torsion (geometricFiber H s₀) (n : ℤ)).X.left, ⊤)) : G ≅ H :=
  isoOfEqualGeometricTorsionOrders hDetermination j hG hH fun n hn s =>
    ((hG.isLocallyConstant_torsionFinrank n hn).apply_eq_of_preconnectedSpace s s₀).trans
      ((h₀ n hn).trans ((hOrder n hn).apply_eq_of_preconnectedSpace s₀ s))

end Langlands.GroupScheme.FibralClopen
