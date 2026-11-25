/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Finite.Etale.FiniteEtaleTowerConeCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible

/-! # Covers mapping to finite etale towers
Source: Stacks Project, Tags 01YW and 0990; finite-stalk adaptation of Tag 09BV.
(blueprint: lem-weil-pbc-finite-etale-tower-cover).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- A finite etale tower with finite nonempty geometric fibers has a compatible
cone whose legs to the base form an affine weakly contractible pro-etale cover.
Source: Stacks Project, Tags 01YW and 0990; finite-stalk adaptation of Tag 09BV.
(blueprint: lem-weil-pbc-finite-etale-tower-cover).
Proof: Pull the tower back to each affine open of X. Its affine inverse limit is
Spec of the direct limit of the rings, and is weakly etale because the rings are
ind-etale. At a geometric point, finite inverse-system compactness gives compatible
points of all stages, hence a point of the affine limit by its limit property.
Thus the limit is surjective over the affine open and its singleton covers.
Refine the limit by affine weakly contractible singleton covers using faithfully
flat ind-etale contractible extensions, and compose with the affine open cover.
The limit projections restrict to the required compatible maps. -/
theorem finite_etale_tower_cover
    (X : Scheme.{u}) (P : ℕ → X.Etale) (p : ∀ n : ℕ, P (n + 1) ⟶ P n)
    (hfin : ∀ n : ℕ, IsFinite (P n).hom)
    (hpoints : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ X) (n : ℕ),
      Finite ((pointSmallEtale x).fiber.obj (P n)) ∧
        Nonempty ((pointSmallEtale x).fiber.obj (P n))) :
    ∃ (J : Type u) (U : J → X.ProEt),
      Presieve.ofArrows (fun j ↦ (U j).left) (fun j ↦ (U j).hom) ∈
          proetalePrecoverage X ∧
      (∀ j : J, IsAffine (U j).left) ∧
      (∀ j : J, (ProEt.topology X).IsWeaklyContractible.{u + 1} (U j)) ∧
      ∃ a : ∀ (j : J) (n : ℕ), U j ⟶ (toProEt X).obj (P n),
        ∀ (j : J) (n : ℕ), a j (n + 1) ≫ (toProEt X).map (p n) = a j n := by
  classical
  obtain ⟨J, U, hc, a, hpa⟩ := finite_etale_tower_cone_cover X P p hfin hpoints
  let C : Cover.{u} proetalePrecoverage X :=
    ⟨⟨J, fun j ↦ (U j).left, fun j ↦ (U j).hom⟩, hc⟩
  let A (j : J) := (U j).left.affineOpenCover
  choose D hD φ hcover hcontract using
    fun (j : J) (k : (A j).I₀) ↦ ProEt.exists_affine_contractible_extension ((A j).X k)
  let (j : J) (k : (A j).I₀) : CommRing (D j k) := hD j k
  let T (j : J) : Cover.{u} proetalePrecoverage (C.X j) :=
    (A j).openCover.weaken (zariskiPrecoverage_le_propQCPrecoverage (P := @WeaklyEtale))
  let H (j : J) (k : (A j).I₀) : Cover.{0} proetalePrecoverage (Spec ((A j).X k)) :=
    .singleton (Spec.map (CommRingCat.ofHom (φ j k))) (hcover j k)
  let V := C.bind (fun j ↦ (T j).bind (H j))
  have hv (i : V.I₀) : WeaklyEtale (V.f i) := Cover.map_prop (Cover.forgetQc V) i
  let W (i : V.I₀) : X.ProEt := ProEt.mk (V.f i)
  let b (i : V.I₀) : W i ⟶ U i.1 :=
    MorphismProperty.Over.homMk (((T i.1).bind (H i.1)).f i.2)
  refine ⟨V.I₀, W, V.mem₀, ?_, ?_, fun i n ↦ b i ≫ a i.1 n, ?_⟩
  · intro i
    change IsAffine (Spec (CommRingCat.of (D i.1 i.2.1)))
    infer_instance
  · intro i F G f hf
    exact hcontract i.1 i.2.1 X (V.f i) _ _ f
      ((Sheaf.isLocallySurjective_iff_epi f).1 hf)
  · intro i n
    rw [Category.assoc, hpa]

end AlgebraicGeometry.Scheme
