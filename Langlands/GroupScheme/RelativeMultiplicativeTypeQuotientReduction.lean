import Langlands.GroupScheme.NormalQuotientFppfOpenGluing
import Langlands.GroupScheme.Descent.AffineFppfQuotient
import Langlands.GroupScheme.RelativeCentralMultiplicativeTypeQuotientStatement
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Reducing multiplicative-type quotients to affine diagonalizable kernels -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- The affine diagonalizable case of affine normal quotient existence. -/
def AffineDiagonalizableNormalQuotientStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsAffine S] (G N : GroupScheme S)
    [IsAffineHom G.X.hom] (i : N ⟶ G),
    IsClosedSubgroup i → (SubgroupFunctor.range i).IsNormal →
    RelativeMultiplicativeType.IsDiagonalizable N →
    ∃ (Q : GroupScheme S) (q : G ⟶ Q), IsAffineHom Q.X.hom ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q

namespace NormalQuotient

/-- A diagonalizable quotient construction on affine bases suffices for any
multiplicative-type normal kernel on an affine base. -/
theorem exists_affine_fppfQuotient_of_multiplicativeType_affine
    (hdiag : AffineDiagonalizableNormalQuotientStatement.{u})
    {S : Scheme.{u}} [IsAffine S] {G N : GroupScheme S}
    [IsAffineHom G.X.hom] (i : N ⟶ G)
    (hi : IsClosedSubgroup i) (hn : (SubgroupFunctor.range i).IsNormal)
    (hN : RelativeMultiplicativeType.IsMultiplicativeType N) :
    ∃ (Q : GroupScheme S) (q : G ⟶ Q), IsAffineHom Q.X.hom ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨U, hU⟩ := hN
  have (j : U.I₀) : Flat (U.f j) := (U.map_prop j).1
  have (j : U.I₀) : LocallyOfFinitePresentation (U.f j) := (U.map_prop j).2
  have : QuasiCompactCover U.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun j => (U.f j).isOpenMap)
  obtain ⟨V, f, hfin, hopen⟩ :
      ∃ (V : Scheme.AffineCover.{u} (@Flat ⊓ @LocallyOfFinitePresentation) S)
        (f : V.cover ⟶ U), Finite V.I₀ ∧ ∀ j, IsOpenImmersion (f.h₀ j) :=
    QuasiCompactCover.exists_hom U
  have : Finite V.cover.I₀ := hfin
  have (j : V.cover.I₀) : IsAffine (V.cover.X j) := by
    change IsAffine (Spec (V.X j))
    infer_instance
  have (j : V.cover.I₀) : Flat (V.cover.f j) := (V.cover.map_prop j).1
  let p : (∐ V.cover.X) ⟶ S := Sigma.desc V.cover.f
  have : IsAffine (∐ V.cover.X) := inferInstance
  have : Flat p := IsZariskiLocalAtSource.sigmaDesc (P := @Flat) (fun j => inferInstance)
  have : Surjective p := inferInstance
  have : QuasiCompact p := inferInstance
  let Gp := (baseChange p).obj G
  let Np := (baseChange p).obj N
  let ip : Np ⟶ Gp := (baseChange p).map i
  have : IsAffineHom Gp.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom p))
  have : IsAffine Gp.X.left := isAffine_of_isAffineHom Gp.X.hom
  have hip : IsClosedSubgroup ip := hi.baseChange p
  let : IsClosedImmersion ip.hom.hom.left := hip
  let : Mono ip.hom.hom := Over.mono_of_mono_left _
  have hnp : (SubgroupFunctor.range ip).IsNormal := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hn.baseChange p
  have hlocal : ∀ j : V.cover.I₀,
      ∃ (Q : GroupScheme (V.cover.X j))
        (q : (baseChange (Sigma.ι V.cover.X j)).obj Gp ⟶ Q),
        IsAffineHom Q.X.hom ∧ RelativeRoot.IsFppfQuotient
          (SubgroupFunctor.range ((baseChange (Sigma.ι V.cover.X j)).map ip)) q := by
    intro j
    have heq : Sigma.ι V.cover.X j ≫ p = f.h₀ j ≫ U.f (f.s₀ j) := by
      rw [f.w₀]
      exact Sigma.ι_comp_desc _ _
    let e := Descent.pullbackComparison p (Sigma.ι V.cover.X j)
      (f.h₀ j ≫ U.f (f.s₀ j)) heq N ≪≫
      baseChangeCompIso (U.f (f.s₀ j)) (f.h₀ j) N
    have hsplit : RelativeMultiplicativeType.IsDiagonalizable
        ((baseChange (Sigma.ι V.cover.X j)).obj Np) :=
      RelativeMultiplicativeType.IsDiagonalizable.of_iso e ((hU (f.s₀ j)).baseChange (f.h₀ j))
    have hn' : (SubgroupFunctor.range
        ((baseChange (Sigma.ι V.cover.X j)).map ip)).IsNormal := by
      rw [SubgroupFunctor.range_baseChangeHom]
      exact hnp.baseChange _
    have : IsAffineHom ((baseChange (Sigma.ι V.cover.X j)).obj Gp).X.hom :=
      inferInstanceAs (IsAffineHom (pullback.snd Gp.X.hom (Sigma.ι V.cover.X j)))
    exact hdiag _ ((baseChange (Sigma.ι V.cover.X j)).obj Gp)
      ((baseChange (Sigma.ι V.cover.X j)).obj Np) _
      (hip.baseChange _) hn' hsplit
  choose Q q hQ hq using hlocal
  obtain ⟨M, r, hM, hr⟩ := exists_affine_fppfQuotient_of_openCover_arbitrary_kernel
    ip hnp (sigmaOpenCover V.cover.X) Q q hQ hq
  let : IsAffineHom M.X.hom := hM
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : QuasiCompact r.hom.hom.left := inferInstance
  obtain ⟨R, a, hR, ha, _⟩ := Descent.exists_affine_fppfQuotient p i M r hr
  let : IsAffine R.X.left := hR
  exact ⟨R, a, inferInstance, ha⟩

/-- The same construction extends to arbitrary bases by open gluing. -/
theorem exists_affine_fppfQuotient_of_multiplicativeType
    (hdiag : AffineDiagonalizableNormalQuotientStatement.{u})
    {S : Scheme.{u}} {G N : GroupScheme S} [IsAffineHom G.X.hom]
    (i : N ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (hN : RelativeMultiplicativeType.IsMultiplicativeType N) :
    ∃ (Q : GroupScheme S) (q : G ⟶ Q), IsAffineHom Q.X.hom ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let U := S.affineCover
  have hlocal : ∀ j : U.I₀,
      ∃ (Q : GroupScheme (U.X j)) (q : (baseChange (U.f j)).obj G ⟶ Q),
        IsAffineHom Q.X.hom ∧ RelativeRoot.IsFppfQuotient
          (SubgroupFunctor.range ((baseChange (U.f j)).map i)) q := by
    intro j
    have : IsAffineHom ((baseChange (U.f j)).obj G).X.hom :=
      inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (U.f j)))
    apply exists_affine_fppfQuotient_of_multiplicativeType_affine hdiag
      ((baseChange (U.f j)).map i) (hi.baseChange _)
    · rw [SubgroupFunctor.range_baseChangeHom]
      exact hn.baseChange _
    · exact hN.baseChange _
  choose Q q hQ hq using hlocal
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  exact exists_affine_fppfQuotient_of_openCover_arbitrary_kernel i hn U Q q hQ hq

end NormalQuotient

/-- The affine diagonalizable normal quotient case implies the published
central multiplicative-type quotient target in the same universe. -/
theorem relativeCentralMultiplicativeTypeQuotient_of_affineDiagonalizable
    (hdiag : AffineDiagonalizableNormalQuotientStatement.{u}) :
    RelativeCentralMultiplicativeTypeQuotientStatement.{u} := by
  intro S G _ hG _ N i hi hc hN
  let := hG
  exact NormalQuotient.exists_affine_fppfQuotient_of_multiplicativeType
    hdiag i hi hc.range_isNormal hN

end Langlands.GroupScheme
