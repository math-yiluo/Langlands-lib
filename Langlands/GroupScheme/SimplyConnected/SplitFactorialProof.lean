import Langlands.GroupScheme.SimplyConnected.SplitFactorialStatement
import Langlands.GroupScheme.SimplyConnected.FactorialAssembly
import Langlands.GroupScheme.Reductive.LocalSplitRootGroupProof
import Langlands.GroupScheme.Reductive.LocalSplitRootDatumExistence
import Langlands.GroupScheme.SplitExistence.IntegralBase
import Langlands.GroupScheme.Reductive.SplitIsogenyRigidityReduction
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.SimplyConnected.CoverPreimageDerived
import Langlands.GroupScheme.Absolute.BorelExistenceCoordinates
import Langlands.AlgebraicGeometry.EtaleNormalLocallyIrreducible
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import Langlands.GroupScheme.Rational.CharacterLatticeProof

/-! # Factoriality of the coordinate ring of a split simply connected group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open SplitFactorial

/-- Coordinate split data exist for every connected reductive group with a split maximal
torus over a field. -/
theorem nonempty_cellData {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] (hG : IsConnectedReductive G) (hT : HasSplitMaximalTorus G) :
    Nonempty (CellData k G) := by
  classical
  obtain ⟨T, i₀, ⟨I, hI, ⟨e⟩⟩, hi₀⟩ := hT
  have : Fintype I := Fintype.ofFinite I
  have hRed := hG.isReductive
  have : Smooth G.X.hom := hG.smooth
  let i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G := e.inv ≫ i₀
  have hmax : IsMaximalTorus (T := splitTorus.commGroupScheme _ I) i :=
    IsMaximalTorus.iso_comp (T' := splitTorus.commGroupScheme _ I) e.symm hi₀
  have hclosed : IsClosedSubgroup i := hmax.2.1
  have hfib : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i :=
    hmax.isFibrewiseMaximalTorus
  obtain ⟨J, P, hP⟩ := localSplitFibrewiseRootDatumExistence k G hRed I i hclosed hfib
  have : Finite J := hP.finite
  have := hP.isReduced
  obtain ⟨b⟩ := SplitExistence.nonempty_base_int P
  obtain ⟨u, hu, hw⟩ := localSplitRootGroup k G hRed I i hclosed hfib J P hP b
  exact ⟨CellData.mk I i hRed hclosed hfib J P hP b u hu hw⟩

/-- **The coordinate ring of a split simply connected group is factorial** (Popov 1974,
Proposition 1 and its Corollary; Milne, *Algebraic Groups* (2017), Corollary 18.24). -/
theorem splitSimplyConnectedFactorial : SplitSimplyConnectedFactorialStatement.{u} := by
  intro k _ G hG hT
  classical
  have hCR := hG.isSemisimple.isConnectedReductive
  have : IsAffineHom G.X.hom := hCR.isAffineHom
  have : Smooth G.X.hom := hCR.smooth
  have : ConnectedSpace G.X.left := hCR.connectedSpace
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsIntegral G.X.left := CoverPreimage.isIntegral_of_smooth_connected G
  have : IsNoetherianRing Γ(G.X.left, ⊤) := BorelExistence.isNoetherianRing_globalSections G
  have hnorm := Langlands.AlgebraicGeometry.EtaleNormalLocallyIrreducible.isDomain_isIntegrallyClosed_sections
    (S := G.X.left) (fun s => Smooth.isDomain_and_isIntegrallyClosed_stalk G.X.hom s)
    (isAffineOpen_top G.X.left)
  have : IsIntegrallyClosed Γ(G.X.left, ⊤) := hnorm.2
  obtain ⟨D⟩ := nonempty_cellData G hCR hT
  obtain ⟨ω, hω⟩ := D.exists_fundamentalWeights hG
  have : Fintype {α // ¬ D.b.IsPos α} := Fintype.ofFinite _
  have : Fintype {α // D.b.IsPos α} := Fintype.ofFinite _
  exact ⟨inferInstance, D.uniqueFactorizationMonoid_of_weights
    (Fintype.equivFin {α // ¬ D.b.IsPos α}).symm (Fintype.equivFin {α // D.b.IsPos α}).symm
    ω hω⟩

end Langlands.GroupScheme
