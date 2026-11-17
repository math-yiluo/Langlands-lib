import Langlands.Geometry.Building.KPMoyPrasadFiltration
import Langlands.GroupScheme.IntegralModel.LieLattice
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-!
# The Lie filtration `𝔤_{x,r}` on supplied data

KP 13.3.3 describes the Moy–Prasad lattice `𝔤_{x,r} ⊆ 𝔤 = Lie(G)` as the `𝒪`-span of a lattice
`z_r ⊆ Lie(Z)`, `Z = Z_G(S)`, and of the Lie lattices `u_ψ ⊆ Lie(U_a)` of the affine roots `ψ`
with derivative `a` and `ψ(x) ≥ r`. This module takes the lattices `z_r` and `u_ψ` as supplied
data (`LieFiltrationData`), and defines from them `𝔤_{x,r}`, the root parts `u_{a,x,r}` and
`𝔤_{x,r+}` at every point `x` of the apartment.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The centralizer `Z = Z_G(S)` is affine over `Spec F`: it is a closed subgroup of `G`. -/
instance centralizer_isAffineHom : IsAffineHom P.centralizer.Z.X.hom := by
  have : IsClosedImmersion P.centralizer.j.hom.hom.left := P.centralizer.isClosedSubgroup
  rw [← P.centralizer.j.hom.hom.w]
  infer_instance

/-- The Lie algebra `u_a = Lie(U_a)` of the root group of a relative root `a`, as an
`𝒪`-submodule of `𝔤 = GenericLie 𝒪 G`: the span of the weight spaces `𝔤_{na}`, `n ≥ 1`
(`RelativeRoot.positiveWeightSpan`). -/
def rootLieSpace (α : relativeRoots P.i) : Submodule 𝒪[F] (GenericLie 𝒪[F] G) :=
  ((RelativeRoot.positiveWeightSpan P.i α.1).comap (GenericLie.equiv 𝒪[F] G).toLinearMap).restrictScalars
    𝒪[F]

theorem mem_rootLieSpace (α : relativeRoots P.i) (X : GenericLie 𝒪[F] G) :
    X ∈ P.rootLieSpace α ↔ GenericLie.equiv 𝒪[F] G X ∈ RelativeRoot.positiveWeightSpan P.i α.1 :=
  Iff.rfl

/-- Supplied lattices for the description of `𝔤_{x,r}` in KP 13.3.3: a decreasing family
`z_r` of `𝒪`-submodules of `Lie(Z)`, and for each affine root `ψ` an `𝒪`-submodule `u_ψ` of
`Lie(G)` contained in `Lie(U_a)`, where `a` is the derivative of `ψ`. -/
structure LieFiltrationData where
  /-- The lattice `z_r` in `Lie(Z)`. -/
  centralizerLie : NNReal → Submodule 𝒪[F] (GenericLie 𝒪[F] P.centralizer.Z)
  centralizerLie_antitone : Antitone centralizerLie
  /-- The lattice `u_ψ` of an affine root `ψ`. -/
  affineRootLie : P.affineRoots → Submodule 𝒪[F] (GenericLie 𝒪[F] G)
  affineRootLie_le : ∀ (ψ : P.affineRoots) (α : relativeRoots P.i),
    ψ.1.linear = rootForm P.i α → affineRootLie ψ ≤ P.rootLieSpace α

namespace LieFiltrationData

variable {P} (L : P.LieFiltrationData)

/-- The image of `z_r` in `𝔤 = Lie(G)` under the differential of `Z → G`. -/
def centralizerLieImage (r : NNReal) : Submodule 𝒪[F] (GenericLie 𝒪[F] G) :=
  (L.centralizerLie r).map (GenericLie.map 𝒪[F] P.centralizer.j)

theorem centralizerLieImage_antitone : Antitone L.centralizerLieImage :=
  fun _ _ h => Submodule.map_mono (L.centralizerLie_antitone h)

/-- The root part `u_{a,x,r}`: the span of the `u_ψ` for the affine roots `ψ` with derivative
`a` and `ψ(x) ≥ r`. -/
def rootLie (x : P.Apartment) (α : relativeRoots P.i) (r : NNReal) :
    Submodule 𝒪[F] (GenericLie 𝒪[F] G) :=
  ⨆ (ψ : P.affineRoots) (_ : ψ.1.linear = rootForm P.i α) (_ : (r : ℝ) ≤ ψ.1 x),
    L.affineRootLie ψ

theorem affineRootLie_le_rootLie {x : P.Apartment} {α : relativeRoots P.i} {r : NNReal}
    (ψ : P.affineRoots) (hψ : ψ.1.linear = rootForm P.i α) (hr : (r : ℝ) ≤ ψ.1 x) :
    L.affineRootLie ψ ≤ L.rootLie x α r :=
  le_iSup₂_of_le ψ hψ (le_iSup_of_le hr le_rfl)

/-- `u_{a,x,r} ⊆ Lie(U_a)`. -/
theorem rootLie_le_rootLieSpace (x : P.Apartment) (α : relativeRoots P.i) (r : NNReal) :
    L.rootLie x α r ≤ P.rootLieSpace α :=
  iSup₂_le fun ψ hψ => iSup_le fun _ => L.affineRootLie_le ψ α hψ

theorem rootLie_antitone (x : P.Apartment) (α : relativeRoots P.i) :
    Antitone (L.rootLie x α) :=
  fun _ _ h => iSup₂_le fun ψ hψ => iSup_le fun hs =>
    L.affineRootLie_le_rootLie ψ hψ ((NNReal.coe_le_coe.2 h).trans hs)

/-- The Moy–Prasad lattice `𝔤_{x,r}` (KP 13.3.3): the `𝒪`-span of `z_r` and of the `u_ψ`
for all affine roots `ψ` with `ψ(x) ≥ r`. -/
def lieFiltration (x : P.Apartment) (r : NNReal) : Submodule 𝒪[F] (GenericLie 𝒪[F] G) :=
  L.centralizerLieImage r ⊔ ⨆ (ψ : P.affineRoots) (_ : (r : ℝ) ≤ ψ.1 x), L.affineRootLie ψ

theorem centralizerLieImage_le_lieFiltration (x : P.Apartment) (r : NNReal) :
    L.centralizerLieImage r ≤ L.lieFiltration x r :=
  le_sup_left

theorem affineRootLie_le_lieFiltration {x : P.Apartment} {r : NNReal} (ψ : P.affineRoots)
    (hr : (r : ℝ) ≤ ψ.1 x) : L.affineRootLie ψ ≤ L.lieFiltration x r :=
  le_sup_of_le_right (le_iSup₂_of_le ψ hr le_rfl)

theorem rootLie_le_lieFiltration (x : P.Apartment) (α : relativeRoots P.i) (r : NNReal) :
    L.rootLie x α r ≤ L.lieFiltration x r :=
  iSup₂_le fun ψ _ => iSup_le fun hr => L.affineRootLie_le_lieFiltration ψ hr

/-- `𝔤_{x,r} = z_r + ∑_a u_{a,x,r}`. -/
theorem lieFiltration_eq_sup_rootLie (x : P.Apartment) (r : NNReal) :
    L.lieFiltration x r = L.centralizerLieImage r ⊔ ⨆ α : relativeRoots P.i, L.rootLie x α r := by
  refine le_antisymm (sup_le_sup_left (iSup₂_le fun ψ hr => ?_) _)
    (sup_le (L.centralizerLieImage_le_lieFiltration x r)
      (iSup_le fun α => L.rootLie_le_lieFiltration x α r))
  obtain ⟨α, hα, -⟩ := ψ.2
  exact le_iSup_of_le α (L.affineRootLie_le_rootLie ψ hα hr)

theorem lieFiltration_antitone (x : P.Apartment) : Antitone (L.lieFiltration x) :=
  fun _ _ h => sup_le_sup (L.centralizerLieImage_antitone h)
    (iSup₂_le fun ψ hs => le_iSup₂_of_le ψ ((NNReal.coe_le_coe.2 h).trans hs) le_rfl)

/-- The lattice `𝔤_{x,r+} = ⋃_{s > r} 𝔤_{x,s}` (KP 13.3.1, convention of KP §1.6). -/
def lieFiltrationPlus (x : P.Apartment) (r : NNReal) : Submodule 𝒪[F] (GenericLie 𝒪[F] G) :=
  ⨆ (s : NNReal) (_ : r < s), L.lieFiltration x s

theorem lieFiltrationPlus_le (x : P.Apartment) (r : NNReal) :
    L.lieFiltrationPlus x r ≤ L.lieFiltration x r :=
  iSup₂_le fun _ hs => L.lieFiltration_antitone x hs.le

theorem lieFiltration_le_lieFiltrationPlus (x : P.Apartment) {r s : NNReal} (h : r < s) :
    L.lieFiltration x s ≤ L.lieFiltrationPlus x r :=
  le_iSup₂_of_le s h le_rfl

end LieFiltrationData

end Langlands.Geometry.Building.ParahoricBuildingData
