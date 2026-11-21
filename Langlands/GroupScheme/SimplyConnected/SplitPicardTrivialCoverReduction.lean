import Langlands.GroupScheme.SimplyConnected.SplitPicardInputsStatement
import Langlands.GroupScheme.SimplyConnected.SplitFactorialStatement
import Langlands.GroupScheme.SimplyConnected.SplitCoverExistenceProof
import Langlands.GroupScheme.CentralIsogeny.SplitMaximalTorusLiftProof
import Langlands.AlgebraicGeometry.Picard.AffineLineBundlePicard
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-! # Reduction of the Picard-trivial central cover to factoriality -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.Picard

/-- On an affine scheme whose ring of global sections has trivial Picard group, every line
bundle is isomorphic to the trivial line bundle. -/
theorem lineBundle_nonempty_iso_trivial_of_isAffine {X : Scheme.{u}} [IsAffine X]
    [Subsingleton (CommRing.Pic Γ(X, ⊤))] (L : LineBundle X) :
    Nonempty (L ≅ LineBundle.trivial X) := by
  let e : X ≅ Spec Γ(X, ⊤) := X.isoSpec
  obtain ⟨t⟩ := nonempty_lineBundle_iso_structureSheaf_of_pic_trivial
    ((LineBundle.pullback e.inv).obj L)
  let t' : (LineBundle.pullback e.inv).obj L ≅ LineBundle.trivial (Spec Γ(X, ⊤)) :=
    ObjectProperty.isoMk _ t
  have hid : Nonempty ((LineBundle.pullback (e.hom ≫ e.inv)).obj L ≅ L) := by
    rw [e.hom_inv_id]
    exact ⟨(LineBundle.pullbackId X).app L⟩
  obtain ⟨u⟩ := hid
  exact ⟨u.symm ≪≫ ((LineBundle.pullbackComp e.hom e.inv).app L).symm ≪≫
    (LineBundle.pullback e.hom).mapIso t' ≪≫ LineBundle.pullbackTrivialIso e.hom⟩

/-- **Reduction.** Factoriality of the coordinate rings of split simply connected groups
implies the existence of a Picard-trivial central cover of every split semisimple group:
take the published simply connected central cover, lift a split maximal torus to it, and
use that a factorial ring has trivial Picard group. -/
theorem splitSemisimplePicardTrivialCover_of_factorial
    (hfac : SplitSimplyConnectedFactorialStatement.{u}) :
    SplitSemisimplePicardTrivialCoverStatement.{u} := by
  intro k _ G hG hsplit
  obtain ⟨T, i, hT, hi⟩ := hsplit
  obtain ⟨C, π, hC, hπ⟩ := splitSimplyConnectedCoverExistence k G T hG hT i hi
  have hCss : IsSemisimple C := hC.isSemisimple
  obtain ⟨T', j, -, hT', hj, -⟩ := centralIsogenySplitMaximalTorusLift k C G
    hCss.isConnectedReductive hG.isConnectedReductive π hπ T i hT hi
  obtain ⟨hdom, hufd⟩ := hfac k C hC ⟨T', j, hT', hj⟩
  have := hdom
  have : UniqueFactorizationMonoid Γ(C.X.left, ⊤) := hufd
  have : IsAffineHom C.X.hom := hCss.isConnectedReductive.isAffineHom
  have : IsAffine C.X.left := isAffine_of_isAffineHom C.X.hom
  exact ⟨C, π, hCss, hπ, fun L => lineBundle_nonempty_iso_trivial_of_isAffine L⟩

end Langlands.GroupScheme
