import Langlands.Geometry.Building.SplitTorusUnitDetection

/-! # Function and morphism detection on bounded split-torus points -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The character-valuation kernel detects a function if its vanishing on every
point of that kernel forces it to be zero. -/
def CharacterKernelDetectsFunctions (v : Valuation k Γ₀)
    (T : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∀ s : Γ(T.X.left, ⊤),
    (∀ x : rationalPoints T, x ∈ characterValuationKernel v T →
      x.left.appTop s = 0) → s = 0

/-- Function detection by character kernels is invariant under group-scheme
isomorphisms. -/
theorem CharacterKernelDetectsFunctions.of_iso (v : Valuation k Γ₀)
    {T U : GroupScheme (Spec (CommRingCat.of k))} (e : T ≅ U)
    (hT : CharacterKernelDetectsFunctions v T) : CharacterKernelDetectsFunctions v U := by
  intro s hs
  have he : e.hom.hom.hom.left.appTop s = 0 := by
    apply hT
    intro x hx
    have hy := map_characterValuationKernel_le v e.hom ⟨x, hx, rfl⟩
    simpa only [rationalPoints.map_apply, Over.comp_left, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply] using hs (rationalPoints.map e.hom x) hy
  have hh := congrArg e.inv.hom.hom.left.appTop he
  simpa only [map_zero, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Over.comp_left, ← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom,
    Over.id_left, Scheme.Hom.id_appTop, CommRingCat.id_apply] using hh

namespace SplitTorusUnitDetection

variable (I : Type u) [Fintype I] [DecidableEq I]

local notation "𝕜" => CommRingCat.of k
local notation "D" => Diagonalizable.groupScheme 𝕜 (I → ℤ)
local notation "e" => Diagonalizable.splitIso 𝕜 (AddEquiv.refl (I → ℤ))

/-- The diagonalizable/split-torus comparison preserves affine coordinates. -/
theorem splitIso_affine_coordinates (S : CommAlgCat 𝕜)
    (x : (algSpec 𝕜).obj (op S) ⟶ (D).X) :
    splitTorus.affinePointsEquiv I ((algSpec 𝕜).obj (op S)).hom
        (x ≫ (e).hom.hom.hom) =
      Diagonalizable.charEquiv (AddEquiv.refl (I → ℤ)) Sˣ
        (Corepresented.affinePointsEquiv _ (Diagonalizable.grpCorepresentation 𝕜 (I → ℤ)) S x) := by
  have hp : splitTorus.pointsEquiv I ((algSpec 𝕜).obj (op S))
      (x ≫ (e).hom.hom.hom) =
      Diagonalizable.splitPointsEquiv 𝕜 (AddEquiv.refl (I → ℤ))
        ((algSpec 𝕜).obj (op S)) x :=
    isoOfPointModels_hom _ _ _ _
      (Diagonalizable.splitPointsEquiv_naturality 𝕜 (AddEquiv.refl (I → ℤ)))
      (fun a y => splitTorus.pointsEquiv_naturality I a y) _ x
  funext i
  apply Units.ext
  change (Scheme.ΓSpecIso (CommRingCat.of S)).hom
    (splitTorus.pointsEquiv I ((algSpec 𝕜).obj (op S)) (x ≫ (e).hom.hom.hom) i).val = _
  rw [hp]
  dsimp only [Diagonalizable.splitPointsEquiv, MulEquiv.trans_apply]
  erw [Corepresented.pointsEquiv_eq_affinePointsEquiv]
  change (Scheme.ΓSpecIso (CommRingCat.of S)).hom
    ((Corepresented.affineSectionsIso S).inv.hom _) = _
  change (Scheme.ΓSpecIso (CommRingCat.of S)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of S)).inv _) = _
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of S)).inv_hom_id _

/-- The rational point of a diagonalizable torus obtained by evaluating its
Laurent monomials on a tuple of field units. -/
def evaluationPoint (t : I → kˣ) : rationalPoints (D).toGrp :=
  let ev := splitTorus.evaluateUnits (R := 𝕜) I t
  Over.homMk (Spec.map (CommRingCat.ofHom ev.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom ev.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k (I → ℤ)))) = 𝟙 _
    rw [← Spec.map_comp]
    convert Spec.map_id 𝕜 using 1
    congr 1
    ext r
    exact ev.commutes r)

/-- Evaluation points have their specified coordinates in the split model. -/
theorem evaluationPoint_coordinates (t : I → kˣ) :
    splitTorus.affinePointsEquiv I (𝟙 (Spec 𝕜))
      (evaluationPoint I t ≫ (e).hom.hom.hom) = t := by
  let ev := splitTorus.evaluateUnits (R := 𝕜) I t
  let x := evaluationPoint I t
  let xA := (algSpec 𝕜).map (CommAlgCat.ofHom ev).op
  have hx : rationalCoeffEquiv k (D).toGrp x = xA := by
    apply Over.OverMorphism.ext
    rw [rationalCoeffEquiv_left]
    rfl
  have hc := splitIso_affine_coordinates I (CommAlgCat.of k k) xA
  have hcoords (i : I) :
      splitTorus.affinePointsEquiv I (𝟙 (Spec 𝕜)) (x ≫ (e).hom.hom.hom) i =
        splitTorus.affinePointsEquiv I ((algSpec 𝕜).obj (op (CommAlgCat.of k k))).hom
          (xA ≫ (e).hom.hom.hom) i := by
    apply Units.ext
    change (Scheme.ΓSpecIso 𝕜).hom
        (splitTorus.pointsEquiv I (Over.mk (𝟙 (Spec 𝕜)))
          (x ≫ (e).hom.hom.hom) i).val =
      (Scheme.ΓSpecIso 𝕜).hom
        (splitTorus.pointsEquiv I ((algSpec 𝕜).obj (op (CommAlgCat.of k k)))
          (xA ≫ (e).hom.hom.hom) i).val
    congr 1
  funext i
  rw [hcoords i, hc]
  dsimp only [xA]
  rw [Corepresented.affinePointsEquiv_map]
  apply Units.ext
  change ev (AddMonoidAlgebra.single (Pi.single i 1) 1) = (t i : k)
  dsimp only [ev]
  rw [splitTorus.evaluateUnits_single (R := 𝕜) I t (Pi.single i 1) 1]
  simp only [map_one, one_mul, splitTorus.exponentValue_single]

/-- The split model's bounded rational points detect every global function. -/
theorem characterKernelDetectsFunctions_split (v : Valuation k Γ₀)
    [Infinite (IsLocalRing.ResidueField v.valuationSubring)] :
    CharacterKernelDetectsFunctions v (splitTorus (Spec 𝕜) I) := by
  intro s hs
  have he : (e).hom.hom.hom.left.appTop s = 0 := by
    apply (Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra k (I → ℤ)))).commRingCatIsoToRingEquiv.injective
    rw [map_zero]
    apply eq_zero_of_evaluateUnits_eq_zero v I
    intro t
    let x := evaluationPoint I (fun i => (t i : kˣ))
    have hx : x ≫ (e).hom.hom.hom ∈
        characterValuationKernel v (splitTorus (Spec 𝕜) I) := by
      rw [mem_split_characterValuationKernel]
      intro i
      rw [evaluationPoint_coordinates]
      exact (mem_valuationOneUnits v (t i)).mp (t i).property
    have hh := hs (x ≫ (e).hom.hom.hom) hx
    change ((Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra k (I → ℤ)))).hom ≫
      CommRingCat.ofHom (splitTorus.evaluateUnits (R := 𝕜) I
        (fun i => (t i : kˣ))).toRingHom) ((e).hom.hom.hom.left.appTop s) = 0
    rw [← Scheme.ΓSpecIso_naturality]
    change (Scheme.ΓSpecIso 𝕜).hom (x.left.appTop ((e).hom.hom.hom.left.appTop s)) = 0
    rw [show x.left.appTop ((e).hom.hom.hom.left.appTop s) = 0 from hh, map_zero]
  have hh := congrArg (e).inv.hom.hom.left.appTop he
  simpa only [map_zero, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Over.comp_left, ← Grp.comp_hom_hom, (e).inv_hom_id, Grp.id_hom_hom,
    Over.id_left, Scheme.Hom.id_appTop, CommRingCat.id_apply] using hh

end SplitTorusUnitDetection

/-- In a split torus, the character-valuation kernel detects regular functions
when the residue field is infinite. -/
theorem characterKernelDetectsFunctions_of_isSplitTorus (v : Valuation k Γ₀)
    [Infinite (IsLocalRing.ResidueField v.valuationSubring)]
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T) :
    CharacterKernelDetectsFunctions v T := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  exact (SplitTorusUnitDetection.characterKernelDetectsFunctions_split I v).of_iso v e.symm

/-- Maps from a split torus to an affine scheme agree when they agree on its
character-valuation kernel. -/
theorem hom_ext_characterValuationKernel (v : Valuation k Γ₀)
    [Infinite (IsLocalRing.ResidueField v.valuationSubring)]
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T)
    {Y : Over (Spec (CommRingCat.of k))} [IsAffine Y.left] {f g : T.X ⟶ Y}
    (h : ∀ x : rationalPoints T, x ∈ characterValuationKernel v T → x ≫ f = x ≫ g) :
    f = g := by
  apply Over.OverMorphism.ext
  apply ext_of_isAffine
  ext s
  apply sub_eq_zero.mp
  apply characterKernelDetectsFunctions_of_isSplitTorus v hT
  intro x hx
  rw [map_sub]
  apply sub_eq_zero.mpr
  have hh := congrArg
    (fun q : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Y => q.left.appTop s) (h x hx)
  simpa only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using hh

end Langlands.Geometry.Building
