/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.AffineSectionsBaseChangeMate
import WeilConjectures.AlgebraicGeometry.PerfectInternalHomPullbackIsIso
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPerfectPart

/-!
# Affine global Hom comparison as sections of sheaf base change

Source: Stacks Project, perfect.tex, Tag 0AA7,
lemma-affine-morphism-and-hom-out-of-perfect, case (1); cohomology.tex, Tag 08I3.
(blueprint: lem-pc-affine-global-hom-base-change-factorization).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The normalized adjunction equations expand the shared derived tensor instances.
/-- The affine global Hom comparison is the sections of the sheaf base-change map
on internal Hom, conjugated by the affine source comparison and the perfect-source
internal-Hom pullback comparison. This statement makes no Tor-independence assumption
and does not assert that either base-change map is invertible.

Source: Stacks Project, perfect.tex, Tag 0AA7,
lemma-affine-morphism-and-hom-out-of-perfect, case (1); cohomology.tex, Tag 08I3.
(blueprint: lem-pc-affine-global-hom-base-change-factorization).

Proof:
1. Put H = RHom(M,K). The perfect tensor-Hom comparison identifies H with the
   tensor of the perfect dual of M and K, so H has quasi-coherent cohomology.
   Since f is qcqs, Rf_*H has quasi-coherent cohomology as well.
2. The derived direct-image composition comparison identifies restricted RΓ_X H
   with RΓ_S Rf_*H. Choose the comparison commuting with the right-derived units;
   on sheaves it is the identity on sections with the R-action induced by f.
3. The affine quasi-coherent derived equivalences on Spec R and Spec B identify
   Lg^* with derived extension of scalars. Compute this comparison on K-flat module
   representatives using the tilde/pullback formula. The extension/restriction
   adjunction on these representatives descends to the derived categories.
   Compare this adjunction with affineDerivedExtensionAdjunction by uniqueness of
   left adjoints to the fixed derived restriction functor. Combining this with
   step 2 gives the source isomorphism a, compatible with the chosen adjunction unit.
4. The canonical map Lg_X^*H → RHom(Lg_X^*M,Lg_X^*K) is invertible. Indeed, rewrite
   H as K tensor the perfect dual of M. Strong monoidal pullback transports the
   evaluation and coevaluation pairing, and the perfect dual pullback comparison
   identifies the transported dual with the internal dual of Lg_X^*M. The tensor-Hom
   evaluation comparison identifies the resulting map with the canonical one:
   after tensoring with Lg_X^*M its evaluation is pullback of evaluation, preceded
   by the inverse tensor-pullback comparison. Apply Rf'_* and RΓ_S' and then the
   unit-compatible direct-image composition comparison to obtain b.
5. Transpose the composite a.hom; RΓ_S'(base change on H); b.hom under the fixed
   extension/restriction adjunction. The source comparison of step 3 commutes with
   its unit. The sheaf base-change map is the mate of the commutative-square
   pullback comparison and the direct-image counit. The triangle identities and
   naturality turn its transpose into restricted RΓ_X of the evaluation-mate map
   of step 4, followed by the sections/pushforward comparison of step 2 on X'.
   This is globalHomPullbackComparison by its evaluation equation and its
   right-derived-unit equation. Injectivity of the adjunction Hom equivalence
   gives the displayed equality. No invertibility of sheaf base change is used. -/
theorem affineGlobalHomBaseChange_factorization
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {R B : CommRingCat.{u}} {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec R) (g : Spec B ⟶ Spec R)
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (M K : schemeDerivedCategory X) (hM : Scheme.IsPerfect X M)
    (hK : schemeDerivedQCohProperty X K) :
    let H := (derivedInternalHom (Opens.grothendieckTopology X)
      X.toRingedSpace.sheaf).obj (op M, K)
    let Γ := affineDerivedGlobalSections (𝟙 (Spec B))
    ∃ a : (affineDerivedExtension g).obj ((schemeGlobalDerivedHomOver f).obj (op M, K)) ≅
        Γ.obj ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj H)),
      ∃ b : Γ.obj ((schemeDerivedDirectImage (pullback.snd f g)).obj
          ((derivedPullback (pullback.fst f g)).obj H)) ≅
          (schemeGlobalDerivedHomOver (pullback.snd f g)).obj
            (op ((derivedPullback (pullback.fst f g)).obj M),
              (derivedPullback (pullback.fst f g)).obj K),
        affineGlobalHomBaseChangeMap f g M K =
          a.hom ≫ Γ.map (schemeDerivedBaseChangeMap f (pullback.snd f g) g
            (pullback.fst f g) pullback.condition H) ≫ b.hom := by
  classical
  let H := (derivedInternalHom (Opens.grothendieckTopology X)
    X.toRingedSpace.sheaf).obj (op M, K)
  let L := (derivedInternalHom (Opens.grothendieckTopology (pullback f g).toRingedSpace)
    (pullback f g).toRingedSpace.sheaf).obj
      (op ((derivedPullback (pullback.fst f g)).obj M),
        (derivedPullback (pullback.fst f g)).obj K)
  let Γ := affineDerivedGlobalSections (𝟙 (Spec B))
  obtain ⟨adj, bS, bT, t, γ, s, c, hadj, hbS, hbT, ht, hγ, hs, hc, hφ⟩ :=
    Classical.choose_spec (exists_globalHomPullbackComparison f g M K)
  subst adj
  have hbSfun := funext hbS
  have hbTfun := funext hbT
  subst bS
  subst bT
  let θ : (derivedPullback (pullback.fst f g)).obj H ⟶ L :=
    ((canonicalPullbackAdjunction (pullback.fst f g)).homEquiv H L).symm
      (γ.app (op M, K))
  have hθ : IsIso θ := by
    have heval := hγ M K
    change θ = _ at heval
    rw [heval]
    exact perfect_internalHom_pullback_isIso (pullback.fst f g) M K hM t ht
  have hH : schemeDerivedQCohProperty X H :=
    rhom_supported_quasiCoherent_perfect_part X M K hK hM
  have hpush : schemeDerivedQCohProperty (Spec R)
      ((schemeDerivedDirectImage f).obj H) :=
    schemeDerivedDirectImage_preserves_QCoh f H hH
  obtain ⟨a, d, hmate⟩ := exists_affineSectionsBaseChangeMate f g H hpush s c hs hc
  let b : Γ.obj ((schemeDerivedDirectImage (pullback.snd f g)).obj
        ((derivedPullback (pullback.fst f g)).obj H)) ≅
      (schemeGlobalDerivedHomOver (pullback.snd f g)).obj
        (op ((derivedPullback (pullback.fst f g)).obj M),
          (derivedPullback (pullback.fst f g)).obj K) :=
    Γ.mapIso ((schemeDerivedDirectImage (pullback.snd f g)).mapIso (asIso θ)) ≪≫ d.app L
  refine ⟨a, b, ?_⟩
  change globalHomPullbackComparison f g M K = _ at hφ
  unfold affineGlobalHomBaseChangeMap
  rw [hφ]
  exact hmate L (γ.app (op M, K))

end AlgebraicGeometry
