import Langlands.GroupScheme.SplitExistence.Normalizing
import Langlands.GroupScheme.SplitExistence.Roots
import Langlands.GroupScheme.Absolute.RegularPerturbation
import Langlands.GroupScheme.Reductive.RootDatum

/-! # The root datum of the Chevalley group

Transporting `P` along `X ≅ X^*(D(X))` (`charEquiv`) and the dual identification
`Y ≅ X_*(D(X))` gives a root datum `chevDatum k P` on the lattices of `D(X)`, isomorphic to `P`.
It is the root datum of the torus `t : D(X) → G` of every Chevalley group `G`:

* its pairing is the Library lattice pairing, by construction of `Y ≅ X_*(D(X))`;
* its roots are the roots of `t` (`ChevGroup.roots_t`);
* each reflection is induced by a point normalizing `t`: for simple roots this is
  `ChevGroup.isNormalizingPoint_weylPoint`, and every root is reached from simple roots by simple
  reflections (`RootPairing.Base.induction_reflect`), realized by conjugating with the simple
  `n_j`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

/-- A root pairing is isomorphic to its transport along linear equivalences. -/
def rootPairingMapEquiv {I R M N M₂ N₂ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing I R M N) (f : M ≃ₗ[R] M₂) (g : N ≃ₗ[R] N₂) :
    RootPairing.Equiv P (P.map (Equiv.refl I) f g) where
  weightMap := f.toLinearMap
  coweightMap := g.symm.toLinearMap
  indexEquiv := Equiv.refl I
  weight_coweight_transpose := by
    ext ν x
    simp [RootPairing.map]
  root_weightMap := by
    ext j
    simp [RootPairing.map]
  coroot_coweightMap := by
    ext j
    simp [RootPairing.map]
  bijective_weightMap := f.bijective
  bijective_coweightMap := g.symm.bijective

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] (k : Type u) [Field k]
  (P : RootDatum J X Y)

section Lattices

variable [Module.Finite ℤ X] [Module.Free ℤ X]

/-- `Y ≅ X_*(D(X))`, dual to `charEquiv` under the two perfect pairings. -/
def cocharEquiv : Y ≃ₗ[ℤ] cocharacterLattice (Tk (X := X) k) :=
  haveI := (isSplitTorus_Tk k P).isPerfPair_latticePairing
  P.flip.toPerfPair.trans ((charEquiv k (X := X)).toIntLinearEquiv.symm.dualMap.trans
    (latticePairing (Tk (X := X) k)).flip.toPerfPair.symm)

theorem latticePairing_charOf_cocharEquiv (x : X) (y : Y) :
    latticePairing (Tk (X := X) k) (charOf k x) (cocharEquiv k P y) = P.toLinearMap x y := by
  have := (isSplitTorus_Tk k P).isPerfPair_latticePairing
  have h : (latticePairing (Tk (X := X) k)).flip.toPerfPair (cocharEquiv k P y) =
      (charEquiv k (X := X)).toIntLinearEquiv.symm.dualMap (P.flip.toPerfPair y) :=
    LinearEquiv.apply_symm_apply _ _
  have h2 := LinearMap.congr_fun h (charEquiv k x)
  rw [← charEquiv_apply]
  simpa using h2

/-- The root datum `P` transported to the lattices of `D(X)`. -/
def chevDatum : RootDatum J (characterLattice (Tk (X := X) k))
    (cocharacterLattice (Tk (X := X) k)) :=
  P.map (Equiv.refl J) (charEquiv k (X := X)).toIntLinearEquiv (cocharEquiv k P)

theorem chevDatum_root (j : J) : (chevDatum k P).root j = charOf k (P.root j) :=
  charEquiv_apply k _

theorem chevDatum_coroot (j : J) : (chevDatum k P).coroot j = cocharEquiv k P (P.coroot j) :=
  rfl

theorem chevDatum_toLinearMap :
    (chevDatum k P).toLinearMap = latticePairing (Tk (X := X) k) := by
  ext χ ν
  obtain ⟨x, rfl⟩ := (charEquiv k (X := X)).surjective χ
  obtain ⟨y, rfl⟩ := (cocharEquiv k P).surjective ν
  rw [charEquiv_apply, latticePairing_charOf_cocharEquiv, ← charEquiv_apply]
  simp [chevDatum, RootPairing.map]

theorem chevDatum_reflection_charOf (α : J) (x : X) :
    (chevDatum k P).reflection α (charOf k x) = charOf k (P.reflection α x) := by
  simp only [RootPairing.reflection_apply, RootPairing.coroot', LinearMap.flip_apply]
  rw [chevDatum_toLinearMap, chevDatum_root, chevDatum_coroot, latticePairing_charOf_cocharEquiv,
    ← charEquiv_apply, ← charEquiv_apply, ← charEquiv_apply, map_sub, map_zsmul]

/-- `P` is isomorphic to `chevDatum k P`. -/
def chevDatumEquiv : RootPairing.Equiv P (chevDatum k P) :=
  rootPairingMapEquiv P _ _

end Lattices

namespace ChevGroup

variable {k P} {b : P.Base} {D : ChevalleyData P b} (G : D.ChevGroup k)

/-- The reflection `s_α` is induced by a point normalizing the torus. -/
def HasNormalizer (α : J) : Prop :=
  ∃ (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.H.X) (σ : Tk (X := X) k ≅ Tk (X := X) k),
    IsNormalizingPoint G.t n σ ∧ ∀ x : X, σ.inv ≫ charOf k x = charOf k (P.reflection α x)

theorem hasNormalizer_simple (i : b.support) : G.HasNormalizer i := by
  refine ⟨G.weylPoint i, _, G.isNormalizingPoint_weylPoint i, fun x => ?_⟩
  rw [torusAut_inv_comp_charOf]
  rfl

theorem hasNormalizer_hom_comp {σ : Tk (X := X) k ≅ Tk (X := X) k} {α : J}
    (h : ∀ x : X, σ.inv ≫ charOf k x = charOf k (P.reflection α x)) (x : X) :
    σ.hom ≫ charOf k x = charOf k (P.reflection α x) := by
  conv_lhs => rw [← P.reflection_same α x, ← h, Iso.hom_inv_id_assoc]

theorem hasNormalizer_reflectionPerm_self {α : J} (h : G.HasNormalizer α) :
    G.HasNormalizer (P.reflectionPerm α α) := by
  obtain ⟨n, σ, hn, hσ⟩ := h
  refine ⟨n, σ, hn, fun x => ?_⟩
  rw [hσ, P.reflection_reflectionPerm]
  simp

theorem hasNormalizer_reflectionPerm {α : J} (h : G.HasNormalizer α) (j : b.support) :
    G.HasNormalizer (P.reflectionPerm j α) := by
  obtain ⟨n, σ, hn, hσ⟩ := h
  obtain ⟨m, τ, hm, hτ⟩ := G.hasNormalizer_simple j
  refine ⟨m * n * m⁻¹, _, (hm.mul hn).mul hm.inv, fun x => ?_⟩
  change ((τ.inv ≫ σ.inv) ≫ τ.hom) ≫ charOf k x = _
  rw [Category.assoc, Category.assoc, hasNormalizer_hom_comp hτ, hσ, hτ,
    P.reflection_reflectionPerm]
  simp

theorem hasNormalizer [Finite J] [P.IsReduced] (α : J) : G.HasNormalizer α :=
  b.induction_reflect α (fun _ h => G.hasNormalizer_reflectionPerm_self h)
    (fun i hi => G.hasNormalizer_simple ⟨i, hi⟩)
    (fun _ j h hj => G.hasNormalizer_reflectionPerm h ⟨j, hj⟩)

/-- **`chevDatum k P` is the root datum of the torus of the Chevalley group.** -/
theorem isRootDatumOf [Finite J] [P.IsReduced] [Module.Finite ℤ X] [Module.Free ℤ X] [IsAffineHom G.H.X.hom] [IsAffine G.H.X.left]
    [LocallyOfFiniteType G.H.X.hom] :
    IsRootDatumOf G.t (chevDatum k P) := by
  refine ⟨chevDatum_toLinearMap k P, ?_, fun α => ?_⟩
  · rw [G.roots_t]
    ext χ
    simp only [Set.mem_range, chevDatum_root]
  · obtain ⟨n, σ, hn, hσ⟩ := G.hasNormalizer α
    refine ⟨n, σ, hn, ?_⟩
    apply LinearEquiv.ext
    intro χ
    obtain ⟨x, rfl⟩ := (charEquiv k (X := X)).surjective χ
    rw [charEquiv_apply, characterAut_apply, hσ, chevDatum_reflection_charOf]

end ChevGroup

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
