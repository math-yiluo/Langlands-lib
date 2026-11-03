import Langlands.GroupScheme.Descent.TensorFullCoverStatement
import Langlands.GroupScheme.SimplyConnected.CoverRecovery
import Langlands.GroupScheme.SimplyConnected.SplitCoverExistenceStatement
import Langlands.GroupScheme.SimplyConnected.SplitFieldExtensionReduction
import Langlands.GroupScheme.SimplyConnected.UniversalPropertyStatement
import Langlands.GroupScheme.Torus.FiniteGaloisSplitMaximal
import Mathlib.FieldTheory.Galois.Basic

/-! # Conditional simple-connectedness ascent through a finite splitting field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme

section FiniteGalois

variable
    (hdescent : SimplyConnectedCoverTensorDescentStatement.{u,u})
    (htensor : ∀ (k L : Type u) [Field k] [Field L] [Algebra k L]
      [FiniteDimensional k L] [IsGalois k L],
      ∃ e : (L ⊗[k] L) ≃ₐ[L] (Gal(L/k) → L),
        ∀ a b σ, e (a ⊗ₜ[k] b) σ = a * σ b)
    (hcover : SplitSimplyConnectedCoverExistenceStatement.{u})
    (hup : SimplyConnectedCentralCoverUniversalProperty.{u})

include hdescent htensor hcover hup in
/-- Descending a full cover proves ascent to a finite Galois splitting field,
with cover existence, its universal property and tensor descent explicit. -/
theorem IsSimplyConnected.fieldExtension_of_finiteGalois_splitMaximalTorus
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSimplyConnected G)
    (hGL : IsSemisimple
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj G))
    (hT : HasSplitMaximalTorus
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj G)) :
    IsSimplyConnected
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj G) := by
  classical
  let baseG := (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj G
  obtain ⟨T, i, hsplit, hi⟩ := hT
  obtain ⟨C, π, hC, hπ⟩ := hcover L baseG T hGL hsplit i hi
  have hfull : IsSimplyConnectedCover π := ⟨hGL, hC, hπ, hup L C baseG π hC hGL hπ⟩
  obtain ⟨e, he⟩ := htensor k L
  obtain ⟨D, a, j, ha, hrec⟩ :=
    hdescent k L (Gal(L/k)) e (fun σ => σ) he G C π hfull
  exact hG.fieldExtension_of_coverRecovery a ha.isSimplyConnected.isSemisimple
    ha.isCentralIsogeny π j hrec hC

set_option linter.defProp false in
include hdescent htensor hcover hup in
/-- A finite Galois splitting field and split coroot ascent give the
algebraic-closure ascent step. All structural inputs remain hypotheses. -/
def isSimplyConnectedAlgebraicClosureAscent_of_tensorDescent
    (hsemi : IsSemisimpleFieldExtensionStatement.{u})
    (hmax : MaximalTorusBaseChangeStatement.{u})
    (hex : RootDatumExistenceStatement.{u})
    (hnec : SplitSimplyConnectedCorootSpanStatement.{u})
    (hsuff : SplitCorootSpanSimplyConnectedStatement.{u})
    (hsplit : TorusFiniteGaloisSplittingStatement.{u}) :
    IsSimplyConnectedAlgebraicClosureAscentStatement.{u} := by
  intro k _ G hG
  obtain ⟨L, _, _, hfin, hgal, hGL, hT⟩ :=
    exists_finiteGalois_hasSplitMaximalTorus_of_isSemisimple hsplit hmax hsemi G
      hG.isSemisimple
  let : FiniteDimensional k L := hfin
  let : IsGalois k L := hgal
  have hGsplit := hG.fieldExtension_of_finiteGalois_splitMaximalTorus
    hdescent htensor hcover hup hGL hT
  let ι : L →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  let : Algebra L (AlgebraicClosure k) := ι.toRingHom.toAlgebra
  let b := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let c := Spec.map (CommRingCat.ofHom ι.toRingHom)
  have hcomp : c ≫ b = toAlgebraicClosure k := by
    dsimp [b, c, toAlgebraicClosure]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    exact RingHom.ext fun x => ι.commutes x
  obtain ⟨T, i, hsplitT, hi⟩ := hT
  have hiter : IsSimplyConnected
      ((baseChange c).obj ((baseChange b).obj G)) :=
    hGsplit.fieldExtension_of_splitMaximalTorus hsemi hmax hex hnec hsuff T
      hsplitT i hi
  have htotal : IsSimplyConnected ((baseChange (c ≫ b)).obj G) :=
    hiter.of_iso (baseChangeCompIso b c G)
  simpa only [hcomp] using htotal

include hdescent htensor hcover hup in
/-- Conditional assembly of arbitrary field-extension ascent from finite tensor
descent, split-cover existence, its universal property and the coroot criteria. -/
theorem isSimplyConnectedFieldExtension_of_tensorDescent_and_corootCriterion
    (hsemi : IsSemisimpleFieldExtensionStatement.{u})
    (hcentral : CentralIsogenyBaseChangeStatement.{u})
    (hmax : MaximalTorusBaseChangeStatement.{u})
    (hex : RootDatumExistenceStatement.{u})
    (hnec : SplitSimplyConnectedCorootSpanStatement.{u})
    (hsuff : SplitCorootSpanSimplyConnectedStatement.{u})
    (hsplit : TorusFiniteGaloisSplittingStatement.{u}) :
    IsSimplyConnectedFieldExtensionStatement.{u} :=
  isSimplyConnectedFieldExtension_of_algebraicClosureAscent_and_corootCriterion
    hsemi hcentral hmax hex hnec hsuff hsplit
    (isSimplyConnectedAlgebraicClosureAscent_of_tensorDescent
      hdescent htensor hcover hup hsemi hmax hex hnec hsuff hsplit)

end FiniteGalois

end Langlands.GroupScheme
