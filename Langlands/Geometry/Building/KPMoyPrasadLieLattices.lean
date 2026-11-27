import Langlands.Geometry.Building.KPMoyPrasadModelStatements
import Langlands.Geometry.Building.KPLieFiltration
import Langlands.Geometry.Building.TorusFiltration.StructuralStatements
import Langlands.Geometry.Building.SpecialTorusExistenceProof
import Langlands.Geometry.Building.UnramifiedValuationDescentProof
import Langlands.GroupScheme.IntegralModel.LieLatticeReduction
import Langlands.GroupScheme.IntegralModel.UnramifiedSmoothHomExtensionProof
import Langlands.GroupScheme.Rational.RootSubgroupRealizationProof
import Langlands.BruhatTits.SpecialCompact.LeviSpecialPoint

/-! # The Lie lattices `𝔤_{x,r} = Lie(𝒢_{x,r})` and their `LieFiltrationData`

KP §13.3.1 defines `𝔤_{x,r}` as the Lie algebra of the smooth model `𝒢_{x,r}` of KP §8.5 and
§9.8.2, and KP 13.3.3 describes it as the `𝒪`-span of the Lie algebra `𝔷_r` of the centralizer
model `𝒵_r` and of the Lie algebras `𝔲_ψ` of the root models `𝒰_ψ` of KP 9.4.5 with
`ψ(x) ≥ r`. This module chooses these models from the existence statements
`MoyPrasadModelStatement`, `CentralizerModelStatement` and `AffineRootGroupModelStatement`, which
enter as explicit hypotheses, and defines

* `moyPrasadLie`: `𝔤_{x,r} = Lie(𝒢_{x,r}) ⊆ Lie(G)` and its strict-depth union `𝔤_{x,r+}`;
* `centralizerModelLie`: `𝔷_r = Lie(𝒵_r) ⊆ Lie(Z)`;
* `affineRootModelLie`: `𝔲_ψ ⊆ Lie(G)`, the image of `Lie(𝒰_ψ)` under the differential of the
  root subgroup `U_a → G`;
* `lieFiltrationData`: the `P.LieFiltrationData` with these lattices.

The lattices of models over `𝒪[F]` depend only on the integral points of the models over the
integers of the maximal unramified extension `K` (`lieLattice_le_of_unramified`, from KP
Corollary 2.10.10); this gives the decreasing property of `𝔷_r`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal ValuativeRel
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.GroupScheme

namespace IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]

/-- A homomorphism of models extending the identity of the generic group carries the Lie
lattice of the source into that of the target. -/
theorem Hom.lieLattice_le_of_id {M N : IntegralModel R K G} (φ : M.Hom N (𝟙 G)) :
    M.lieLattice ≤ N.lieLattice := by
  intro X hX
  have h := φ.map_lieLattice_le (Submodule.mem_map_of_mem (f := GenericLie.map R (𝟙 G)) hX)
  rwa [GenericLie.map_id] at h

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]

/-- **KP Corollary 2.10.10 for Lie lattices.** If `M` is a smooth model of `G` over `𝒪[F]`
whose integral points over the integers of the maximal unramified extension lie in those of
`N`, then the identity of `G` extends to a homomorphism `M → N`, so `Lie(M) ⊆ Lie(N)`. -/
theorem lieLattice_le_of_unramified {M N : IntegralModel ↥𝒪[F] F G} (hM : M.IsSmooth)
    (h : M.baseChangeUnramified.integralPoints ≤ N.baseChangeUnramified.integralPoints) :
    M.lieLattice ≤ N.lieLattice := by
  obtain ⟨φ⟩ := unramifiedSmoothHomExtension F G G (𝟙 G) M N hM (fun g hg => by
    rw [CategoryTheory.Functor.map_id]
    have hid : rationalPoints.map (𝟙 (baseChanged F (inertiaFixedField F) G)) g = g := by
      simp only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id]
    rw [hid]
    exact h hg)
  exact φ.lieLattice_le_of_id

/-- **KP Corollary 2.10.11 for Lie lattices.** Two smooth models of `G` over `𝒪[F]` with the
same integral points over the integers of the maximal unramified extension have the same Lie
lattice. -/
theorem lieLattice_eq_of_unramified {M N : IntegralModel ↥𝒪[F] F G} (hM : M.IsSmooth)
    (hN : N.IsSmooth)
    (h : M.baseChangeUnramified.integralPoints = N.baseChangeUnramified.integralPoints) :
    M.lieLattice = N.lieLattice :=
  le_antisymm (lieLattice_le_of_unramified hM h.le) (lieLattice_le_of_unramified hN h.ge)

end Unramified

end IntegralModel

namespace RelativeRoot

variable {k : Type u} [Field k] (R : Type u) [CommRing R] [Algebra R k]
  {G U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [IsAffineHom U.X.hom]

/-- If `j : U ⟶ G` represents a subgroup functor whose tangent image is `W`, then the
differential of `j` takes values in `W`. -/
theorem map_mem_of_hasLieImage {F : SubgroupFunctor G}
    {W : Submodule k (Additive (lieKernel G k))} {j : U ⟶ G} (hj : F.IsRepresentedBy j)
    (hW : HasLieImage F W) (X : GenericLie R U) :
    GenericLie.equiv R G (GenericLie.map R j X) ∈ W := by
  apply (hW _).1
  rw [← hj.2]
  exact ⟨(GenericLie.equiv R U X).toMul.val, rfl⟩

end RelativeRoot

end Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

private instance lieLatticesBaseChangeAffineHom :
    IsAffineHom (baseChanged F (UnramifiedClosure F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (UnramifiedClosure F)))
  infer_instance

/-! ### A chosen apartment lift -/

/-- A special torus containing the maximal split torus of `P`, with an apartment lift to the
maximal unramified extension, chosen using the published existence of special tori and of
unramified valuation descent. -/
def unramifiedApartmentLift : Σ t : P.UnramifiedComparisonTorus, t.ApartmentLift :=
  Classical.choice <| by
    obtain ⟨t, ⟨L⟩⟩ := exists_unramifiedApartmentLift
      specialTorusExistence unramifiedValuationDescent P
    exact ⟨⟨t, L⟩⟩

/-! ### The models `𝒢_{x,r}` and the lattices `𝔤_{x,r}` -/

section MoyPrasad

variable (hG : MoyPrasadModelStatement.{u}) (hP : P.SatisfiesApartmentAxioms)
  (h : P.MinimalCongruentCentralizerOrder)

/-- The smooth model `𝒢_{x,r}` of `G` over `𝒪[F]` of KP §9.8.2 at the constant concave
function `r`, chosen from `MoyPrasadModelStatement` for the chosen apartment lift. -/
def moyPrasadModel (x : P.Apartment) (r : ℝ≥0) : IntegralModel ↥𝒪[F] F G :=
  (hG F G P hP h P.unramifiedApartmentLift.1 P.unramifiedApartmentLift.2 x r).choose

theorem moyPrasadModel_isSmooth (x : P.Apartment) (r : ℝ≥0) :
    (P.moyPrasadModel hG hP h x r).IsSmooth :=
  (hG F G P hP h P.unramifiedApartmentLift.1 P.unramifiedApartmentLift.2 x r).choose_spec.1

theorem moyPrasadModel_hasGeometricallyConnectedFibres (x : P.Apartment) (r : ℝ≥0) :
    (P.moyPrasadModel hG hP h x r).HasGeometricallyConnectedFibres :=
  (hG F G P hP h P.unramifiedApartmentLift.1 P.unramifiedApartmentLift.2 x r).choose_spec.2.1

/-- The integral points of `𝒢_{x,r}` over the integers of `K` are `G(K)_{x,r}`. -/
theorem moyPrasadModel_unramifiedIntegralPoints (x : P.Apartment) (r : ℝ≥0) :
    (P.moyPrasadModel hG hP h x r).baseChangeUnramified.integralPoints =
      P.unramifiedApartmentLift.2.buildingData.minimalCongruentMoyPrasad
        P.unramifiedApartmentLift.2.centralizer_isTorus (P.unramifiedApartmentLift.2.e x) r :=
  (hG F G P hP h P.unramifiedApartmentLift.1 P.unramifiedApartmentLift.2 x r).choose_spec.2.2.1

/-- The integral points of `𝒢_{x,r}` over `𝒪[F]` are `P_{x,r}`. -/
theorem moyPrasadModel_integralPoints (x : P.Apartment) (r : ℝ≥0) :
    (P.moyPrasadModel hG hP h x r).integralPoints = P.minimalCongruentMoyPrasad h x r :=
  (hG F G P hP h P.unramifiedApartmentLift.1 P.unramifiedApartmentLift.2 x r).choose_spec.2.2.2

/-- The Moy–Prasad lattice `𝔤_{x,r} = Lie(𝒢_{x,r})` of KP §13.3.1, an `𝒪[F]`-submodule of
`Lie(G)`. -/
def moyPrasadLie (x : P.Apartment) (r : ℝ≥0) : Submodule 𝒪[F] (GenericLie 𝒪[F] G) :=
  (P.moyPrasadModel hG hP h x r).lieLattice

/-- `𝔤_{x,r}` is an `𝒪[F]`-lattice in `Lie(G)` (KP §13.3.1). -/
theorem moyPrasadLie_isLattice (x : P.Apartment) (r : ℝ≥0) :
    Submodule.IsLattice F (P.moyPrasadLie hG hP h x r) :=
  IntegralModel.lieLattice_isLattice (P.moyPrasadModel_isSmooth hG hP h x r)

/-- `𝔤_{x,r+} = ⋃_{s > r} 𝔤_{x,s}` (KP §13.3.1 with the convention of KP §1.6), as a
supremum of submodules. -/
def moyPrasadLiePlus (x : P.Apartment) (r : ℝ≥0) : Submodule 𝒪[F] (GenericLie 𝒪[F] G) :=
  ⨆ (s : ℝ≥0) (_ : r < s), P.moyPrasadLie hG hP h x s

theorem moyPrasadLie_le_moyPrasadLiePlus (x : P.Apartment) {r s : ℝ≥0} (hrs : r < s) :
    P.moyPrasadLie hG hP h x s ≤ P.moyPrasadLiePlus hG hP h x r :=
  le_iSup₂_of_le s hrs le_rfl

end MoyPrasad

/-! ### The centralizer models `𝒵_r` and the lattices `𝔷_r` -/

section Centralizer

variable (hZ : CentralizerModelStatement.{u})

/-- The smooth model `𝒵_r` of `Z = Z_G(S)` over `𝒪[F]` of KP 13.3.3, chosen from
`CentralizerModelStatement`. -/
def centralizerModel (r : ℝ≥0) : IntegralModel ↥𝒪[F] F P.centralizer.Z :=
  (hZ F G P r).choose

theorem centralizerModel_isSmooth (r : ℝ≥0) : (P.centralizerModel hZ r).IsSmooth :=
  (hZ F G P r).choose_spec.1

/-- The integral points of `𝒵_r` over the integers of `K` are `Z(K)_{x₀,r}`. -/
theorem centralizerModel_unramifiedIntegralPoints (r : ℝ≥0) :
    (P.centralizerModel hZ r).baseChangeUnramified.integralPoints =
      P.centralizerUnramifiedApartmentLift.2.buildingData.minimalCongruentMoyPrasad
        P.centralizerUnramifiedApartmentLift.2.centralizer_isTorus
        (P.centralizerUnramifiedApartmentLift.2.e P.centralizerBuildingPoint) r :=
  (hZ F G P r).choose_spec.2.2.1

/-- The integral points of `𝒵_r` over `𝒪[F]` are `Z(F)_r`. -/
theorem centralizerModel_integralPoints (r : ℝ≥0) :
    (P.centralizerModel hZ r).integralPoints = P.minimalCongruentCentralizerPoints r :=
  (hZ F G P r).choose_spec.2.2.2.1

/-- The lattice `𝔷_r = Lie(𝒵_r) ⊆ Lie(Z)` of KP 13.3.3. -/
def centralizerModelLie (r : ℝ≥0) : Submodule 𝒪[F] (GenericLie 𝒪[F] P.centralizer.Z) :=
  (P.centralizerModel hZ r).lieLattice

/-- `𝔷_r` decreases with `r`: the minimal congruent torus filtration decreases
(`MinimalCongruentOrderStatement`), hence so does `Z(K)_{x₀,r}`, and smooth models with smaller
integral points over the integers of `K` have smaller Lie lattices. -/
theorem centralizerModelLie_antitone (hOrder : MinimalCongruentOrderStatement.{u}) :
    Antitone (P.centralizerModelLie hZ) := by
  intro r s hrs
  apply IntegralModel.lieLattice_le_of_unramified (P.centralizerModel_isSmooth hZ s)
  rw [P.centralizerModel_unramifiedIntegralPoints hZ s,
    P.centralizerModel_unramifiedIntegralPoints hZ r]
  set L := P.centralizerUnramifiedApartmentLift.2
  exact L.buildingData.moyPrasadWith_antitone
    (hOrder F (L.buildingData.centralizerTorus L.centralizer_isTorus) L.centralizer_isTorus).1
    (L.e P.centralizerBuildingPoint) hrs

end Centralizer

/-! ### Root groups and the root models `𝒰_ψ` -/

section Roots

/-- A representative `U_a` of the root subgroup of the relative root `a`, chosen from
`RelativeRoot.rootSubgroupRealization`. -/
def rootGroupScheme (α : relativeRoots P.i) : GroupScheme (Spec (CommRingCat.of F)) :=
  (RelativeRoot.rootSubgroupRealization F G P.isConnectedReductive P.S P.i
    P.isMaximalSplitTorus α.1 α.2).choose

/-- The inclusion `U_a ⟶ G` of the chosen root subgroup representative. -/
def rootGroupInclusion (α : relativeRoots P.i) : P.rootGroupScheme α ⟶ G :=
  (RelativeRoot.rootSubgroupRealization F G P.isConnectedReductive P.S P.i
    P.isMaximalSplitTorus α.1 α.2).choose_spec.choose

theorem rootGroupInclusion_isRepresentedBy (α : relativeRoots P.i) :
    (RelativeRoot.subgroup P.i α.1).IsRepresentedBy (P.rootGroupInclusion α) :=
  (RelativeRoot.rootSubgroupRealization F G P.isConnectedReductive P.S P.i
    P.isMaximalSplitTorus α.1 α.2).choose_spec.choose_spec.1

theorem rootGroupInclusion_isClosedSubgroup (α : relativeRoots P.i) :
    IsClosedSubgroup (P.rootGroupInclusion α) :=
  (RelativeRoot.rootSubgroupRealization F G P.isConnectedReductive P.S P.i
    P.isMaximalSplitTorus α.1 α.2).choose_spec.choose_spec.2.1

theorem rootGroupInclusion_hasLieImage (α : relativeRoots P.i) :
    RelativeRoot.HasLieImage (RelativeRoot.subgroup P.i α.1)
      (RelativeRoot.positiveWeightSpan P.i α.1) :=
  (RelativeRoot.rootSubgroupRealization F G P.isConnectedReductive P.S P.i
    P.isMaximalSplitTorus α.1 α.2).choose_spec.choose_spec.2.2.2.2.2.2.2

/-- The chosen root subgroup representative is affine over `F`: it is a closed subgroup of the
affine group `G`. -/
instance rootGroupScheme_isAffineHom (α : relativeRoots P.i) :
    IsAffineHom (P.rootGroupScheme α).X.hom := by
  have : IsClosedImmersion (P.rootGroupInclusion α).hom.hom.left :=
    P.rootGroupInclusion_isClosedSubgroup α
  rw [← (P.rootGroupInclusion α).hom.hom.w]
  infer_instance

/-- The relative root `a` of an affine root `ψ`: its derivative is `rootForm a`. -/
def affineRootDerivative (ψ : P.affineRoots) : relativeRoots P.i := ψ.2.choose

theorem affineRootDerivative_spec (ψ : P.affineRoots) :
    ψ.1.linear = rootForm P.i (P.affineRootDerivative ψ) :=
  ψ.2.choose_spec.1

/-- The relative root of an affine root is unique, since `S` is split. -/
theorem eq_affineRootDerivative (ψ : P.affineRoots) {α : relativeRoots P.i}
    (hα : ψ.1.linear = rootForm P.i α) : α = P.affineRootDerivative ψ :=
  Langlands.BruhatTits.SpecialCompact.rootForm_injective_of_split
    P.isMaximalSplitTorus.isSplitSubtorus.1 P.i (hα.symm.trans (P.affineRootDerivative_spec ψ))

variable (hU : AffineRootGroupModelStatement.{u}) (hP : P.SatisfiesApartmentAxioms)

/-- The smooth model `𝒰_ψ` over `𝒪[F]` of the root group `U_a` of KP 9.4.5, `a` the
derivative of the affine root `ψ`, chosen from `AffineRootGroupModelStatement`. -/
def affineRootModel (ψ : P.affineRoots) :
    IntegralModel ↥𝒪[F] F (P.rootGroupScheme (P.affineRootDerivative ψ)) :=
  (hU F G P hP ψ (P.affineRootDerivative ψ) (P.affineRootDerivative_spec ψ)
    (P.rootGroupScheme (P.affineRootDerivative ψ)) (P.rootGroupInclusion (P.affineRootDerivative ψ))
    (P.rootGroupInclusion_isRepresentedBy (P.affineRootDerivative ψ))).choose

theorem affineRootModel_isSmooth (ψ : P.affineRoots) : (P.affineRootModel hU hP ψ).IsSmooth :=
  (hU F G P hP ψ (P.affineRootDerivative ψ) (P.affineRootDerivative_spec ψ)
    (P.rootGroupScheme (P.affineRootDerivative ψ)) (P.rootGroupInclusion (P.affineRootDerivative ψ))
    (P.rootGroupInclusion_isRepresentedBy (P.affineRootDerivative ψ))).choose_spec.1

/-- The integral points of `𝒰_ψ` over `𝒪[F]` have the image `U_ψ` in `G(F)`. -/
theorem affineRootModel_integralPoints (ψ : P.affineRoots) :
    (P.affineRootModel hU hP ψ).integralPoints.map
        (rationalPoints.map (P.rootGroupInclusion (P.affineRootDerivative ψ))) =
      P.affineRootGroup (P.affineRootDerivative ψ) ψ.1 :=
  (hU F G P hP ψ (P.affineRootDerivative ψ) (P.affineRootDerivative_spec ψ)
    (P.rootGroupScheme (P.affineRootDerivative ψ)) (P.rootGroupInclusion (P.affineRootDerivative ψ))
    (P.rootGroupInclusion_isRepresentedBy (P.affineRootDerivative ψ))).choose_spec.2.2.2

/-- The lattice `𝔲_ψ ⊆ Lie(G)` of KP 13.3.3: the image of `Lie(𝒰_ψ)` under the differential of
the root subgroup inclusion `U_a → G`. -/
def affineRootModelLie (ψ : P.affineRoots) : Submodule 𝒪[F] (GenericLie 𝒪[F] G) :=
  (P.affineRootModel hU hP ψ).lieLattice.map
    (GenericLie.map 𝒪[F] (P.rootGroupInclusion (P.affineRootDerivative ψ)))

/-- `𝔲_ψ ⊆ Lie(U_a)`: the differential of a representative of the root subgroup takes values in
the positive weight spaces of `a`. -/
theorem affineRootModelLie_le_rootLieSpace (ψ : P.affineRoots) (α : relativeRoots P.i)
    (hα : ψ.1.linear = rootForm P.i α) : P.affineRootModelLie hU hP ψ ≤ P.rootLieSpace α := by
  obtain rfl := P.eq_affineRootDerivative ψ hα
  rintro _ ⟨X, -, rfl⟩
  rw [mem_rootLieSpace]
  exact RelativeRoot.map_mem_of_hasLieImage 𝒪[F] (P.rootGroupInclusion_isRepresentedBy _)
    (P.rootGroupInclusion_hasLieImage _) X

end Roots

/-! ### The `LieFiltrationData` -/

/-- The `LieFiltrationData` of KP 13.3.3 built from the constructed models: `z_r = Lie(𝒵_r)`
and `u_ψ = Lie(𝒰_ψ)` (`affineRootModelLie`). Its `lieFiltration x r` is the `𝒪[F]`-span of the
image of `Lie(𝒵_r)` and of the `Lie(𝒰_ψ)` with `ψ(x) ≥ r`. -/
def lieFiltrationData (hZ : CentralizerModelStatement.{u}) (hU : AffineRootGroupModelStatement.{u})
    (hOrder : MinimalCongruentOrderStatement.{u}) (hP : P.SatisfiesApartmentAxioms) :
    P.LieFiltrationData where
  centralizerLie := P.centralizerModelLie hZ
  centralizerLie_antitone := P.centralizerModelLie_antitone hZ hOrder
  affineRootLie := P.affineRootModelLie hU hP
  affineRootLie_le := P.affineRootModelLie_le_rootLieSpace hU hP

@[simp] theorem lieFiltrationData_centralizerLie (hZ : CentralizerModelStatement.{u})
    (hU : AffineRootGroupModelStatement.{u}) (hOrder : MinimalCongruentOrderStatement.{u})
    (hP : P.SatisfiesApartmentAxioms) (r : ℝ≥0) :
    (P.lieFiltrationData hZ hU hOrder hP).centralizerLie r = (P.centralizerModel hZ r).lieLattice :=
  rfl

@[simp] theorem lieFiltrationData_affineRootLie (hZ : CentralizerModelStatement.{u})
    (hU : AffineRootGroupModelStatement.{u}) (hOrder : MinimalCongruentOrderStatement.{u})
    (hP : P.SatisfiesApartmentAxioms) (ψ : P.affineRoots) :
    (P.lieFiltrationData hZ hU hOrder hP).affineRootLie ψ =
      (P.affineRootModel hU hP ψ).lieLattice.map
        (GenericLie.map 𝒪[F] (P.rootGroupInclusion (P.affineRootDerivative ψ))) :=
  rfl

end Langlands.Geometry.Building.ParahoricBuildingData
