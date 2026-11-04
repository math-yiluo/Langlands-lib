import Langlands.GroupScheme.Cartan.CentralTorusQuotient
import Langlands.GroupScheme.Absolute.NoCocharacterUnipotent
import Langlands.GroupScheme.Nilpotent.TorusCentrality
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityStatement
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # Empty torus roots and geometric nilpotence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- An empty root support for a split-torus action makes its zero weight
space the whole actual Lie algebra. -/
theorem weightSpace_zero_eq_top_of_roots_eq_empty
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : roots i = ∅) : weightSpace i 0 = ⊤ := by
  classical
  apply top_unique
  rw [← (isInternal_weightSpace_of_isSplitTorus k G T hT i).submodule_iSup_eq_top]
  refine iSup_le fun χ => ?_
  by_cases hχ : χ = 0
  · subst χ
    exact le_rfl
  · have hbot : weightSpace i χ = ⊥ := by
      by_contra hn
      have hroot : χ ∈ roots i := ⟨hχ, hn⟩
      rw [hi] at hroot
      exact hroot
    rw [hbot]
    exact bot_le

/-- A split-torus homomorphism with no adjoint roots is central on every
scheme test when the ambient group is smooth, connected and affine. -/
theorem isCentral_of_roots_eq_empty
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : roots i = ∅) : IsCentral i := by
  have : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  have hInv : (AutomorphicAction.conjugation i).lieInvariants = ⊤ := by
    apply top_unique
    intro X _
    have hX : X ∈ weightSpace i 0 := by
      rw [weightSpace_zero_eq_top_of_roots_eq_empty hT i hi]
      trivial
    intro A _ _ t
    rw [AutomorphicAction.differential_conjugation]
    simpa only [Lie.characterValue_zero, Units.val_one, one_smul] using hX A t
  classical
  obtain ⟨I, hfin, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  let := Module.Finite.iff_addGroup_fg.mp (inferInstance : Module.Finite ℤ (I → ℤ))
  let d := e ≪≫
    (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ))).symm
  apply (isCentral_iff_torusCentralizer_eq_top i).2
  have h := AutomorphicAction.fixedSubgroup_eq_top_of_diagonalizable_lieInvariants_eq_top
    (AutomorphicAction.conjugation i) d hInv
  rwa [AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer] at h

variable [IsAlgClosed k]

/-- Over an algebraically closed field, the actual quotient by a central
maximal torus is unipotent. -/
theorem CentralMaximalTorusQuotientData.isUnipotent_of_isAlgClosed
    (D : CentralMaximalTorusQuotientData G) : IsUnipotent D.quotient := by
  let := D.smooth_quotient
  let := D.affine_quotient
  let := D.connected_quotient
  apply AbsoluteNoCocharacter.isUnipotent
  intro z
  exact SubgroupFunctor.eq_zero_of_range_eq_bot
    (D.no_tori _ isSplitTorus_gm.isTorus z)

/-- The same quotient gives an all-test nilpotence bound, without assuming
the arbitrary-field no-torus unipotence theorem. -/
theorem CentralMaximalTorusQuotientData.exists_hasUniformNilpotentPoints_of_isAlgClosed
    (D : CentralMaximalTorusQuotientData G) :
    ∃ d, HasUniformNilpotentPoints G d :=
  D.exists_hasUniformNilpotentPoints D.isUnipotent_of_isAlgClosed

/-- A central maximal torus forces geometric nilpotence over an
algebraically closed field. -/
theorem IsMaximalTorus.isNilpotentGroupScheme_of_isCentral_of_isAlgClosed
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    {i : T.toGrp ⟶ G} (hi : IsMaximalTorus i) (hc : IsCentral i) :
    IsNilpotentGroupScheme G := by
  obtain ⟨d, hd⟩ := (hi.centralQuotient hc).exists_hasUniformNilpotentPoints_of_isAlgClosed
  exact hd.isNilpotentGroupScheme

/-- A maximal torus with empty adjoint root support forces geometric
nilpotence over an algebraically closed field. -/
theorem IsMaximalTorus.isNilpotentGroupScheme_of_roots_eq_empty
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    {i : T.toGrp ⟶ G} (hi : IsMaximalTorus i) (hroot : roots i = ∅) :
    IsNilpotentGroupScheme G :=
  hi.isNilpotentGroupScheme_of_isCentral_of_isAlgClosed
    (isCentral_of_roots_eq_empty
      (hi.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting) i hroot)

/-- The empty-root criterion over algebraically closed fields, at every universe. -/
def EmptyRootsNilpotenceStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
    IsMaximalTorus i → roots i = ∅ → IsNilpotentGroupScheme G

theorem emptyRootsNilpotence : EmptyRootsNilpotenceStatement.{u} := by
  intro k _ _ G _ _ _ T i hi hroot
  exact hi.isNilpotentGroupScheme_of_roots_eq_empty hroot

end Langlands.GroupScheme
