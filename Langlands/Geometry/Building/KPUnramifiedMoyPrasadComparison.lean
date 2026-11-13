import Langlands.Geometry.Building.KPLocalMoyPrasadGroupProperties
import Langlands.Geometry.Building.KPUnramifiedRationalMoyPrasadStatement

/-!
# Comparison of building data over `F` and `K = F^ur` (KP §9.6, §9.8)

KP §9.8 obtains the properties of `G(K)_{x,r} ∩ G(F)` from the group properties of the
groups `G(K)_{x,r}` (KP §7.3, §8.5, §13.2) and from the comparison of the building data of
`G` over `F` with building data of `G_K` over `K` (KP Construction 9.6.1, Lemma 9.6.3,
Theorem 9.6.5). This module states that comparison as a Prop-valued structure
`ParahoricBuildingData.IsUnramifiedComparison P B hZ e`, for building data `P` over `F`,
building data `B` over `K` with torus centralizer and a map `e` of apartments. It proves that
the published group properties of `G(K)_{x,r}`
(`MaximalUnramified.LocalMoyPrasadGroupPropertiesStatement`) together with such a
comparison make `y, r ↦ G(K)_{e y,r} ∩ G(F)` a rational Moy–Prasad family. Neither the group
properties nor the existence of a comparison is proved here.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal commutatorElement
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

private instance unramifiedComparisonAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (UnramifiedClosure F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (UnramifiedClosure F)))
  infer_instance

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The comparison at one relative root `a` of `(G, S)`, for a set `Ψ` of relative roots of
`(G_K, S_K)` (meant: those restricting to `a` or `2a`) and a cocharacter `ν` of `S_K` (meant:
a generic element of the image of the cocharacter space of `S` with `⟨a, ν⟩ > 0`).
Write `ι : G(F) → G(K)` and `j : Z(F) → G(F)`. -/
structure IsUnramifiedRootComparison
    (B : MaximalUnramified.BuildingData F (baseChanged F (UnramifiedClosure F) G))
    (e : P.Apartment → B.Apartment) (a : relativeRoots P.i)
    (Ψ : Set (characterLattice B.S)) (ν : V B.S) : Prop where
  /-- `Ψ` is a closed set of relative roots. -/
  closed : B.IsClosedRootSet Ψ
  /-- `Ψ` lies in the open half-space `⟨·, ν⟩ > 0`. -/
  pos : ∀ b ∈ Ψ, 0 < eval B.S b ν
  /-- `ι(U_a(F)) ⊆ U_Ψ(K)`. -/
  root_mem : ∀ g ∈ P.rootGroup a.1,
    rationalExtend F (UnramifiedClosure F) G g ∈ B.rootGroupSpan Ψ
  /-- `ι(U_{-a}(F)) ⊆ U_{-ν}(K)`, the span of the root groups `U_b(K)` with `⟨b, ν⟩ < 0`. -/
  neg_mem : ∀ g ∈ P.rootGroup (-a.1),
    rationalExtend F (UnramifiedClosure F) G g ∈ B.rootGroupSpan (B.negativePairingRoots ν)
  /-- `ι(j(Z(F))) ⊆ M_ν(K)`. -/
  levi_mem : ∀ z : rationalPoints P.centralizer.Z,
    rationalExtend F (UnramifiedClosure F) G (rationalPoints.map P.centralizer.j z) ∈
      B.pairingLeviSpan ν
  /-- `ι(U_{a,y,s}) ⊆ ⟨U_{b,e y,s} | b ∈ Ψ⟩`. -/
  filtration_mem : ∀ (y : P.Apartment) (s : ℝ≥0), ∀ g ∈ P.filtration y a.1 s,
    rationalExtend F (UnramifiedClosure F) G g ∈ B.rootFiltrationSpan (e y) Ψ s
  /-- Descent of the filtration: if `g ∈ U_a(F)` and `ι g ∈ ⟨U_{b,e y,t} | b ∈ Ψ⟩`, then
  `g ∈ U_{a,y,t} U_{2a,y,t}`. -/
  block_mem : ∀ (y : P.Apartment) (t : ℝ≥0), ∀ g ∈ P.rootGroup a.1,
    rationalExtend F (UnramifiedClosure F) G g ∈ B.rootFiltrationSpan (e y) Ψ t →
      g ∈ P.apartment.filtrationBlock y (fun _ => (t : ℝ)) a.1

/-- The comparison of building data `P` of `G` over `F` with building data `B` of `G_K` over
`K = F^ur` whose centralizer is a torus (`hZ`), along a map `e` of apartments
(KP Construction 9.6.1, Lemma 9.6.3, Theorem 9.6.5 and §9.8). Write
`ι : G(F) → G(K)` and `j : Z(F) → G(F)`. -/
structure IsUnramifiedComparison
    (B : MaximalUnramified.BuildingData F (baseChanged F (UnramifiedClosure F) G))
    (hZ : IsTorus B.centralizer.Z) (e : P.Apartment → B.Apartment) : Prop where
  /-- `e` intertwines `N(F)` with its image in `G(K)`, in the reduced building over `K`. -/
  apartmentMap_smul : ∀ (n : normalizerPoints P.i) (y : P.Apartment),
    B.apartmentMap (e (n • y)) =
      rationalExtend F (UnramifiedClosure F) G (n : rationalPoints G) • B.apartmentMap (e y)
  /-- The comparison at each relative root. -/
  rootComparison : ∀ a : relativeRoots P.i,
    ∃ (Ψ : Set (characterLattice B.S)) (ν : V B.S), P.IsUnramifiedRootComparison B e a Ψ ν
  /-- For some `ν`, `ι(j(Z(F))) ⊆ M_ν(K)` and the points `e y` have the same valuation at the
  roots of `M_ν`. -/
  levi : ∃ ν : V B.S,
    (∀ z : rationalPoints P.centralizer.Z,
      rationalExtend F (UnramifiedClosure F) G (rationalPoints.map P.centralizer.j z) ∈
        B.pairingLeviSpan ν) ∧
    ∀ (y y' : P.Apartment), ∀ b ∈ B.zeroPairingRoots ν, (e y).val b = (e y').val b
  /-- Depth zero: `j⁻¹(ι⁻¹(G(K)_{e y,0})) = Z(F)^0`. -/
  comap_zero : ∀ y : P.Apartment,
    ((B.moyPrasad hZ (e y) 0).comap (rationalExtend F (UnramifiedClosure F) G)).comap
      (rationalPoints.map P.centralizer.j) = P.centralizerZero
  /-- The groups `j⁻¹(ι⁻¹(G(K)_{e y,r}))` are open in `Z(F)` for the point topology. -/
  isOpen :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : IsAffine P.centralizer.Z.X.left := by
      have : IsClosedImmersion P.centralizer.j.hom.hom.left :=
        P.centralizer.isClosedSubgroup
      exact isAffine_of_isAffineHom P.centralizer.j.hom.hom.left
    letI : TopologicalSpace (rationalPoints P.centralizer.Z) :=
      rationalPointTopology F P.centralizer.Z.X
    ∀ (y : P.Apartment) (r : ℝ≥0),
      IsOpen ((((B.moyPrasad hZ (e y) r).comap
        (rationalExtend F (UnramifiedClosure F) G)).comap
          (rationalPoints.map P.centralizer.j) : Subgroup _) :
        Set (rationalPoints P.centralizer.Z))

private theorem rationalExtend_injective' :
    Function.Injective (rationalExtend F (UnramifiedClosure F) G) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro x y h
  apply (rationalCoeffEquiv F G).injective
  apply GaloisPoint.extend_injective F (UnramifiedClosure F) G
  simpa only [baseChangeCoeffEquiv_rationalExtend] using
    congrArg (baseChangeCoeffEquiv F (UnramifiedClosure F) G) h

private theorem centralizer_map_injective' :
    Function.Injective (rationalPoints.map P.centralizer.j) := by
  let : Mono P.centralizer.j.hom.hom := P.centralizer.isRepresentedBy.1
  intro x y hxy
  exact (cancel_mono P.centralizer.j.hom.hom).mp hxy

/-- `⟨U_{b,x,r} | b ∈ Ψ⟩ ⊆ ⟨U_{b,x',r} | b ∈ Ψ⟩` when `U_{b,x,r} ⊆ U_{b,x',r}` for `b ∈ Ψ`. -/
private theorem rootFiltrationSpan_mono
    {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    [IsAffineHom H.X.hom] (B : MaximalUnramified.BuildingData F H) (x x' : B.Apartment)
    (Ψ : Set (characterLattice B.S)) (r : ℝ)
    (h : ∀ b ∈ Ψ, B.filtration x b r ≤ B.filtration x' b r) :
    B.rootFiltrationSpan x Ψ r ≤ B.rootFiltrationSpan x' Ψ r := by
  unfold MaximalUnramified.BuildingData.rootFiltrationSpan
  exact iSup₂_mono h

variable {P}

local notation "ιK" => rationalExtend F (UnramifiedClosure F) G
local notation "jF" => rationalPoints.map P.centralizer.j

namespace IsUnramifiedComparison

variable {B : MaximalUnramified.BuildingData F (baseChanged F (UnramifiedClosure F) G)}
  {hZ : IsTorus B.centralizer.Z} {e : P.Apartment → B.Apartment}
  (hC : P.IsUnramifiedComparison B hZ e)

include hC

/-- The `Z(F)`-part of `G(K)_{e y,r}` does not depend on `y` (Levi intersection). -/
theorem mem_moyPrasad_of_mem (hLevi : MaximalUnramified.LocalMoyPrasadLeviIntersection B hZ)
    (y y' : P.Apartment) (r : ℝ≥0) (z : rationalPoints P.centralizer.Z)
    (hz : ιK (jF z) ∈ B.moyPrasad hZ (e y) r) : ιK (jF z) ∈ B.moyPrasad hZ (e y') r := by
  obtain ⟨ν, hlevi, hval⟩ := hC.levi
  have hfb : ∀ b ∈ B.zeroPairingRoots ν,
      B.filtration (e y) b (r : ℝ) = B.filtration (e y') b (r : ℝ) := by
    intro b hb
    ext g
    rw [KPApartmentData.mem_filtration, KPApartmentData.mem_filtration, hval y y' b hb]
  have hle : B.rootFiltrationSpan (e y) (B.zeroPairingRoots ν) r ≤
      B.rootFiltrationSpan (e y') (B.zeroPairingRoots ν) r :=
    rootFiltrationSpan_mono B (e y) (e y') _ _ fun b hb => (hfb b hb).le
  have h1 : ιK (jF z) ∈ B.pairingLeviSpan ν ⊓ B.moyPrasad hZ (e y) r :=
    Subgroup.mem_inf.2 ⟨hlevi z, hz⟩
  have h : B.pairingLeviSpan ν ⊓ B.moyPrasad hZ (e y) r ≤
      B.pairingLeviSpan ν ⊓ B.moyPrasad hZ (e y') r := by
    rw [hLevi ν (e y) r, hLevi ν (e y') r]
    exact sup_le_sup_left hle _
  exact (Subgroup.mem_inf.1 (h h1)).2

/-- `U_{b,y,s} ⊆ ι⁻¹(G(K)_{e y,s})`. -/
theorem filtration_le (y : P.Apartment) (b : relativeRoots P.i) (s : ℝ≥0) :
    P.filtration y b.1 s ≤ (B.moyPrasad hZ (e y) s).comap ιK := by
  obtain ⟨Ψ, ν, hR⟩ := hC.rootComparison b
  have hspan : B.rootFiltrationSpan (e y) Ψ s ≤ B.moyPrasad hZ (e y) s :=
    iSup₂_le fun c hc => B.filtration_le_moyPrasad hZ (e y) ⟨c, hR.closed.1 hc⟩ s
  intro g hg
  exact Subgroup.mem_comap.2 (hspan (hR.filtration_mem y s g hg))

omit hC in
/-- `[ι⁻¹(G(K)_{x,r}), ι⁻¹(G(K)_{x,s})] ⊆ ι⁻¹(G(K)_{x,r+s})`. -/
theorem commutator_le (hComm : MaximalUnramified.LocalMoyPrasadCommutator B hZ)
    (x : B.Apartment) (r s : ℝ≥0) :
    ⁅(B.moyPrasad hZ x r).comap ιK, (B.moyPrasad hZ x s).comap ιK⁆ ≤
      (B.moyPrasad hZ x (r + s)).comap ιK := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  rw [Subgroup.mem_comap, map_commutatorElement]
  exact hComm x r s (Subgroup.commutator_mem_commutator (Subgroup.mem_comap.1 hg₁)
    (Subgroup.mem_comap.1 hg₂))

/-- `n ι⁻¹(G(K)_{e y,r}) n⁻¹ ⊆ ι⁻¹(G(K)_{e (n y),r})` for `n ∈ N(F)`. -/
theorem conj_mem (hEquiv : MaximalUnramified.LocalMoyPrasadEquivariance B hZ)
    (n : normalizerPoints P.i) (y : P.Apartment) (r : ℝ≥0) (g : rationalPoints G)
    (hg : ιK g ∈ B.moyPrasad hZ (e y) r) :
    ιK ((n : rationalPoints G) * g * (n : rationalPoints G)⁻¹) ∈
      B.moyPrasad hZ (e (n • y)) r := by
  rw [← hEquiv.1 (ιK (n : rationalPoints G)) (e y) (e (n • y)) (hC.apartmentMap_smul n y) r,
    map_mul, map_mul, map_inv]
  exact Subgroup.mem_map_of_mem (MulAut.conj (ιK (n : rationalPoints G))).toMonoidHom hg

/-- Positive-depth Iwahori factorization of `ι⁻¹(G(K)_{e y,t})`. -/
theorem map_mem_of_mul_mem (hIwahori : MaximalUnramified.LocalMoyPrasadIwahoriFactorization B hZ)
    (y : P.Apartment) (a : relativeRoots P.i) (t : ℝ≥0) (ht : 0 < t)
    (v' : rationalPoints G) (hv' : v' ∈ P.rootGroup (-a.1))
    (v : rationalPoints G) (hv : v ∈ P.rootGroup a.1) (z : rationalPoints P.centralizer.Z)
    (hmem : ιK v' * ιK (jF z) * ιK v ∈ B.moyPrasad hZ (e y) t) :
    ιK (jF z) ∈ B.moyPrasad hZ (e y) t := by
  obtain ⟨Ψ, ν, hR⟩ := hC.rootComparison a
  have hpos : B.rootGroupSpan Ψ ≤ B.rootGroupSpan (B.positivePairingRoots ν) :=
    biSup_mono fun b hb => ⟨hR.closed.1 hb, hR.pos b hb⟩
  exact (hIwahori ν (e y) t ht (ιK v') (hR.neg_mem v' hv') (ιK (jF z)) (hR.levi_mem z)
    (ιK v) (hpos (hR.root_mem v hv)) hmem).2.1

omit hC in
/-- The `Z(F)`-parts of `ι⁻¹(G(K)_{e y,r})` are separated. -/
theorem iInf_comap (hSep : MaximalUnramified.LocalMoyPrasadSeparated B hZ) (y : P.Apartment) :
    ⨅ r : ℝ≥0, ((B.moyPrasad hZ (e y) r).comap ιK).comap jF = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : ιK (jF z) ∈ ⨅ r : ℝ≥0, B.moyPrasad hZ (e y) r :=
    Subgroup.mem_iInf.2 fun r =>
      Subgroup.mem_comap.1 (Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hz r))
  rw [hSep (e y), Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  apply P.centralizer_map_injective'
  apply rationalExtend_injective'
  rw [hz', map_one, map_one]

/-- `U_a(F) ∩ ι⁻¹(G(K)_{e y,t}) ⊆ U_{a,y,t} U_{2a,y,t}`. -/
theorem mem_filtrationBlock (hRoot : MaximalUnramified.LocalMoyPrasadRootIntersection B hZ)
    (y : P.Apartment) (a : relativeRoots P.i) (t : ℝ≥0) (g : rationalPoints G)
    (hg : g ∈ P.rootGroup a.1) (hgt : ιK g ∈ B.moyPrasad hZ (e y) t) :
    g ∈ P.apartment.filtrationBlock y (fun _ => (t : ℝ)) a.1 := by
  obtain ⟨Ψ, ν, hR⟩ := hC.rootComparison a
  have h : ιK g ∈ B.rootGroupSpan Ψ ⊓ B.moyPrasad hZ (e y) t :=
    Subgroup.mem_inf.2 ⟨hR.root_mem g hg, hgt⟩
  rw [hRoot Ψ ν hR.closed hR.pos (e y) t] at h
  exact hR.block_mem y t g hg h

end IsUnramifiedComparison

/-- **The rational Moy–Prasad family from a comparison with `K = F^ur`** (KP Lemma 9.8.1,
Proposition 9.8.3 and their proofs). Given the group properties of the groups `G(K)_{x,r}`
and a comparison of `P` with building data `B` over `K`, the groups
`G(K)_{e y,r} ∩ G(F) = ι⁻¹(G(K)_{e y,r})` form a rational Moy–Prasad family. -/
theorem isRationalMoyPrasadFamily_of_unramifiedComparison
    (hS2 : MaximalUnramified.LocalMoyPrasadGroupPropertiesStatement.{u})
    {B : MaximalUnramified.BuildingData F (baseChanged F (UnramifiedClosure F) G)}
    {hZ : IsTorus B.centralizer.Z} {e : P.Apartment → B.Apartment}
    (hC : P.IsUnramifiedComparison B hZ e) :
    P.IsRationalMoyPrasadFamily (fun y r => (B.moyPrasad hZ (e y) r).comap ιK) := by
  obtain ⟨-, hEquiv, hComm, hRoot, hIwahori, hLevi, -, hSep⟩ :=
    hS2 F (baseChanged F (UnramifiedClosure F) G) B hZ
  exact
    { antitone := fun y _ _ h => Subgroup.comap_mono (B.moyPrasad_antitone hZ (e y) h)
      filtration_le := fun y b s => hC.filtration_le y b s
      commutator_le := fun y r s => IsUnramifiedComparison.commutator_le hComm (e y) r s
      conj_mem := fun n y r g hg => Subgroup.mem_comap.2
        (hC.conj_mem hEquiv n y r g (Subgroup.mem_comap.1 hg))
      map_mem_of_mul_mem := fun y a t ht v' hv' v hv z hmem => Subgroup.mem_comap.2
        (hC.map_mem_of_mul_mem hIwahori y a t ht v' hv' v hv z (by
          have h := Subgroup.mem_comap.1 hmem
          rwa [map_mul, map_mul] at h))
      comap_eq := fun y y' r => by
        ext z
        exact ⟨hC.mem_moyPrasad_of_mem hLevi y y' r z, hC.mem_moyPrasad_of_mem hLevi y' y r z⟩
      comap_zero := hC.comap_zero
      iInf_comap := IsUnramifiedComparison.iInf_comap hSep
      mem_filtrationBlock := fun y a t g hg hgt =>
        hC.mem_filtrationBlock hRoot y a t g hg (Subgroup.mem_comap.1 hgt)
      isOpen := hC.isOpen }

end ParahoricBuildingData

/-- **Reduction of the F-to-K link of KP §9.8.** The group properties of the groups
`G(K)_{x,r}` and the existence of a comparison of every `P` with building data over
`K = F^ur` imply `UnramifiedRationalMoyPrasadStatement`. -/
theorem unramifiedRationalMoyPrasad_of_unramifiedComparison
    (hS2 : MaximalUnramified.LocalMoyPrasadGroupPropertiesStatement.{u})
    (hC : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
      (P : ParahoricBuildingData G), P.SatisfiesApartmentAxioms →
        ∃ (B : MaximalUnramified.BuildingData F (baseChanged F (UnramifiedClosure F) G))
          (hZ : IsTorus B.centralizer.Z) (e : P.Apartment → B.Apartment),
          P.IsUnramifiedComparison B hZ e) :
    UnramifiedRationalMoyPrasadStatement.{u} := by
  intro F _ _ _ _ G _ P hP
  obtain ⟨B, hZ, e, hBe⟩ := hC F G P hP
  exact ⟨B, hZ, e, ParahoricBuildingData.isRationalMoyPrasadFamily_of_unramifiedComparison
    hS2 hBe⟩

end Langlands.Geometry.Building
