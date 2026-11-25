/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
import WeilConjectures.Topology.Sheaves.GrothendieckVanishing
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.CategoryTheory.SpectralSequence.Vanishing
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleCore

/-!
# From affine to global torsion cohomological dimension

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
`lemma-uniform-bounds-pro-etale-affines`, Leray comparison step (blueprint:
lemma-uniform-bounds-pro-etale-affines).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

open CategoryTheory.Limits TopologicalSpace Opposite in
/-- Transfer Grothendieck vanishing to coefficients one universe above the base space. -/
private theorem zariski_derived_dimension_bound
    (X : Type u) [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    [HasInjectiveResolutions
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1})]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1})
    (n : ℕ) (hn : d < n) :
    IsZero (((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation (TopologicalSpace.Opens X)ᵒᵖ AddCommGrpCat.{u + 1}).obj
        (op ⊤)).rightDerived n).obj F) := by
  let Y := ULift.{u + 1} X
  let H : Y ≃ₜ X := Homeomorph.ulift
  let e : TopologicalSpace.Opens Y ≌ TopologicalSpace.Opens X := H.opensCongr.equivalence
  let J := Opens.grothendieckTopology X
  let K := Opens.grothendieckTopology Y
  let : e.inverse.IsDenseSubsite J K := {
    functorPushforward_mem_iff := by
      intro U S
      constructor
      · intro hs x hx
        obtain ⟨V, f, ⟨Z, g, a, hg, _⟩, hv⟩ := hs (ULift.up x) hx
        exact ⟨Z, g, hg, a.le hv⟩
      · intro hs x hx
        obtain ⟨V, f, hf, hv⟩ := hs x.down hx
        exact ⟨e.inverse.obj V, e.inverse.map f,
          S.image_mem_functorPushforward e.inverse hf, hv⟩ }
  let T := (e.sheafCongr K J AddCommGrpCat.{u + 1}).inverse
  let ΓX := sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation (TopologicalSpace.Opens X)ᵒᵖ AddCommGrpCat.{u + 1}).obj (op ⊤)
  let ΓY : Sheaf K AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
    Sheaf.sectionsFunctorAt K (⊤ : TopologicalSpace.Opens Y)
  let : IsGrothendieckAbelian.{u + 1} (Sheaf J AddCommGrpCat.{u + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u + 1} J AddCommGrpCat.{u + 1}
  let : T.Additive := Functor.additive_of_preserves_binary_products T
  let : NoetherianSpace Y := (noetherianSpace_iff_of_homeomorph H).mpr inferInstance
  let : QuasiSober Y := H.isOpenEmbedding.quasiSober
  have hy : topologicalKrullDim Y < (n : WithBot ℕ∞) :=
    lt_of_le_of_lt (H.isInducing.topologicalKrullDim_le.trans hd) (by exact_mod_cast hn)
  have hh : Subsingleton (Sheaf.H (T.obj F) n) :=
    TopCat.Sheaf.subsingleton_H_of_topologicalKrullDim_lt (X := TopCat.of Y) (T.obj F) hy
  have hz : IsZero ((ΓY.rightDerived n).obj (T.obj F)) :=
    (Sheaf.subsingleton_H_iff_isZero_rightDerived K isTerminalTop n (T.obj F)).mp hh
  let a : ΓX ≅ T ⋙ ΓY := NatIso.ofComponents (fun G ↦
    G.obj.mapIso (eqToIso (show e.functor.obj ⊤ = ⊤ by ext; rfl)).op) (by
    intro A B f
    exact (f.hom.naturality _).symm)
  have hz' := hz.of_iso (Functor.compRightDerivedObjIso T ΓY
    (fun I _ ↦ Functor.rightAcyclic_of_injective (F := ΓY) (T.obj I)) n F)
  exact hz'.of_iso ((NatIso.rightDerived a n).app F)

open CategoryTheory.Limits TopologicalSpace Opposite in
/-- Exactness on the affine basis implies exactness of a short complex of Zariski sheaves. -/
private theorem exact_of_affine_sections
    (X : Scheme.{u})
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1}))
    (h : ∀ U : X.Opens, IsAffineOpen U →
      (S.map (sheafToPresheaf _ _ ⋙
        (CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op U))).Exact) :
    S.Exact := by
  let k := kernel.lift S.g S.f S.zero
  apply S.exact_iff_epi_kernel_lift.mpr
  suffices Sheaf.IsLocallySurjective k from Sheaf.epi_of_isLocallySurjective k
  change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) k.hom
  constructor
  intro U s x hx
  obtain ⟨V, hV, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
  let t := (kernel S.g).obj.map (homOfLE hVU).op s
  let z := (kernel.ι S.g).hom.app (op V) t
  have hz : S.g.hom.app (op V) z = 0 := by
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun f ↦ f.hom) (kernel.condition S.g)) (op V)) t
  obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).mp (h V hV) z hz
  refine ⟨V, homOfLE hVU, ⟨y, ?_⟩, hxV⟩
  have hmono : Function.Injective ((kernel.ι S.g).hom.app (op V)) :=
    (AddCommGrpCat.mono_iff_injective _).mp
      ((sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op V)).map_mono (kernel.ι S.g))
  apply hmono
  change (kernel.ι S.g).hom.app (op V) (k.hom.app (op V) y) = z
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, kernel.lift_ι]
  exact hy

open CategoryTheory.Limits TopologicalSpace Opposite in
/-- Open restriction preserves injectives, so affine cohomology computes section homology. -/
private theorem isZero_affine_section_homology
    {X : Scheme.{u}} (i : X.Opens ⥤ X.Etale)
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F) (n : ℕ) (U : X.Opens)
    (h : Subsingleton (Sheaf.H
      ((Etale.openImmersionRestriction AddCommGrpCat.{u + 1} U.ι).obj F) n)) :
    IsZero (((Sheaf.sectionsFunctorAt X.smallEtaleTopology (i.obj U)).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex |>.homology n) := by
  let R := Etale.openImmersionRestriction AddCommGrpCat.{u + 1} U.ι
  let Γ : Sheaf (U : Scheme).smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      AddCommGrpCat.{u + 1} := Sheaf.sectionsFunctorAt (U : Scheme).smallEtaleTopology
    (Scheme.Etale.mk (𝟙 (U : Scheme)))
  let E := Sheaf.sectionsFunctorAt X.smallEtaleTopology (i.obj U)
  let : R.IsLeftAdjoint :=
    (Etale.openImmersionRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι).isLeftAdjoint
  let : R.PreservesInjectiveObjects :=
    (Etale.openImmersionLowerShriekAdjunction AddCommGrpCat.{u + 1}
      U.ι).preservesInjectiveObjects_of_preservesFiniteLimits
  have hz : IsZero ((Γ.rightDerived n).obj (R.obj F)) :=
    (Sheaf.subsingleton_H_iff_isZero_rightDerived _
      (MorphismProperty.Over.mkIdTerminal @Etale (U : Scheme)) n (R.obj F)).mp h
  have eobj : (Scheme.Etale.forget X).obj (i.obj U) =
      (Scheme.Etale.forget X).obj (Scheme.Etale.mk (𝟙 (U : Scheme) ≫ U.ι)) := by
    change (i ⋙ Scheme.Etale.forget X).obj U = (Over.mk U.ι)
    rw [hi]
    rfl
  let eU := (Scheme.Etale.forget X).preimageIso (eqToIso eobj)
  let e : E ≅ R ⋙ Γ := NatIso.ofComponents (fun G ↦ G.obj.mapIso eU.op.symm) (by
    intro A B f
    exact (f.hom.naturality _).symm)
  have hz' : IsZero (((R ⋙ Γ).rightDerived n).obj F) :=
    hz.of_iso (Functor.compRightDerivedObjIso R Γ
      (fun A _ ↦ Functor.rightAcyclic_of_injective (F := Γ) (R.obj A)) n F)
  exact (hz'.of_iso ((NatIso.rightDerived e n).app F)).of_iso
    (I.isoRightDerivedObj E n).symm

open CategoryTheory.Limits TopologicalSpace Opposite in
/-- Vanishing of restricted cohomology on every affine open kills the comparison derivative. -/
private theorem isZero_comparison_rightDerived_of_affine_sections
    {X : Scheme.{u}} (i : X.Opens ⥤ X.Etale)
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    [i.IsContinuous (Opens.grothendieckTopology X) X.smallEtaleTopology]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (h : ∀ U : X.Opens, IsAffineOpen U → Subsingleton (Sheaf.H
      ((Etale.openImmersionRestriction AddCommGrpCat.{u + 1} U.ι).obj F) n)) :
    let P := i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X) X.smallEtaleTopology
    let _ : P.Additive := Functor.additive_of_preserves_binary_products P
    IsZero ((P.rightDerived n).obj F) := by
  dsimp
  let P := i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X) X.smallEtaleTopology
  let : P.Additive := Functor.additive_of_preserves_binary_products P
  let I := injectiveResolution F
  let K := (P.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  have hz : IsZero (K.homology n) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    apply exact_of_affine_sections X (K.sc n)
    intro U hU
    change (((Sheaf.sectionsFunctorAt X.smallEtaleTopology (i.obj U)).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex).ExactAt n
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact isZero_affine_section_homology i hi F I n U (h U hU)
  exact hz.of_iso (I.isoRightDerivedObj P n)

-- Preserve the names of the original hypothesis binders.
set_option linter.unusedVariables false in
/-- The comparison and Leray step turns the affine bound into the bound for a
finite-type scheme.

Source: the comparison-site proof of `lemma-uniform-bounds-pro-etale-affines` in the
blueprint subsection `sec-smooth-purity/sk-prop-sf-cbc`.

Proof: X is Noetherian: it is locally Noetherian by local finite type over a
field and quasi-compact by quasi-compactness of its structure morphism. Let
ε be the morphism from the small etale site to the Zariski site, whose direct
image evaluates F on open subschemes. Its inverse image is exact, so its right
adjoint preserves injectives. Abelian sheaves on either site form Grothendieck
abelian categories (equivalently modules over the constant integer sheaf), and
Zariski sections are left exact. The Grothendieck spectral sequence therefore
has E₂^{p,r} = H^p(X_Zar, R^r ε_*F). Evaluation at the terminal open identifies
Γ_Zar ε_* with Γ_et, so its abutment is H^{p+r}(X_et,F).

For each point x the stalk of R^r ε_*F is the filtered colimit over open
neighbourhoods V of H^r(V_et,F|V). Indeed apply ε_* to an injective resolution;
open restriction preserves injectives and filtered colimits of abelian groups
are exact, so cohomology commutes with that colimit. Affine neighbourhoods are
cofinal: refine an intersection of two neighbourhoods to a smaller affine
neighbourhood, without asserting that the intersection is affine. Such a V
is affine and finite type over K, and its dimension is at most d since closure
in X preserves strict chains of irreducible closed subsets of V. Restricting
F preserves the locally torsion condition: each local annihilating cover over
V is the same cover in the localized etale site. Thus hAffine makes the
colimit zero for r > d + c. Stalks detect zero Zariski sheaves, so R^r ε_*F = 0
in those degrees. Grothendieck vanishing on the Noetherian space X kills the
E₂ terms for p > d, for every abelian Zariski sheaf, without a torsion condition.
If p + r = q > 2 * d + c, either p > d or r > d + c. Thus all E₂ terms of
total degree q are zero, as are their later pages. First-quadrant convergence
gives a finite filtration of H^q with zero graded pieces, and therefore H^q = 0.
The same argument covers the empty scheme and d = 0; no separatedness of X is
used. The field cohomological-dimension hypothesis is unnecessary here: it is
used only to supply hAffine in the parent theorem.
(blueprint: new-thm-sc-finite-type-torsion-cd-affine-reduction)
-/
theorem subsingleton_H_of_two_mul_add_lt_of_affine_bound
    {K : Type u} [Field K] (c d : ℕ)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (hAffine : ∀ {Y : Scheme.{u}} (b : Y ⟶ Spec (.of K)) [LocallyOfFiniteType b]
      [QuasiCompact b] [IsAffine Y] (hY : topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
      (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : G.IsTorsion) (n : ℕ),
      d + c < n → Subsingleton (Sheaf.H G n))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : 2 * d + c < q) : Subsingleton (Sheaf.H F q) :=
    open CategoryTheory.Limits TopologicalSpace Opposite in by
  classical
  obtain ⟨i, hi, _, hlim, ⟨htop⟩, hcont, hflat⟩ := zariski_to_etale_core X
  let := hcont
  let := hlim
  let := hflat
  let J := Opens.grothendieckTopology X.carrier
  let P := i.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J X.smallEtaleTopology
  let L := i.sheafPullback AddCommGrpCat.{u + 1} J X.smallEtaleTopology
  let : IsGrothendieckAbelian.{u + 1} (Sheaf J AddCommGrpCat.{u + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u + 1} J AddCommGrpCat.{u + 1}
  let Γ := Sheaf.sectionsFunctorAt J (⊤ : X.Opens)
  have hL : PreservesFiniteLimits L := by
    let : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
      AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
    have := preservesFiniteLimits_op_lan_of_flat
      (H := AddCommGrpCat.{u + 1}) i
    exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _
  let := hL
  have hP : P.Additive := Functor.additive_of_preserves_binary_products P
  let := hP
  have hΓ : Γ.Additive := inferInstance
  let := hΓ
  have hFG : P.IsAcyclicComposablePair Γ :=
    (i.sheafAdjunctionContinuous AddCommGrpCat.{u + 1} J
      X.smallEtaleTopology).isAcyclicComposablePair Γ
  -- Check the pushed-forward resolution on affine opens, avoiding stalk colimits.
  have hR : ∀ n : ℕ, d + c < n → IsZero ((P.rightDerived n).obj F) := by
    intro n hn
    apply isZero_comparison_rightDerived_of_affine_sections i hi F n
    intro U hU
    let : IsAffine (U : Scheme) := hU
    have hdim : topologicalKrullDim (U : Scheme) ≤ (d : WithBot ℕ∞) :=
      (topologicalKrullDim_subspace_le X (U : Set X)).trans hX
    have hu := hAffine (U.ι ≫ a) hdim
      ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj F)
      (Etale.isTorsion_upperStar U.ι hF) n hn
    let e := (Sheaf.functorH (U : Scheme).smallEtaleTopology n).mapIso
      ((Etale.upperStarIsoOpenImmersionRestriction AddCommGrpCat.{u + 1} U.ι).app F)
    exact e.addCommGroupIsoToAddEquiv.subsingleton_congr.mp hu
  have hZ : ∀ p n : ℕ, d < p →
      IsZero ((Γ.rightDerived p).obj ((P.rightDerived n).obj F)) := by
    intro p n hp
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian a
    let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
    let : IsNoetherian X := IsNoetherian.mk
    exact zariski_derived_dimension_bound X d hX ((P.rightDerived n).obj F) p hp
  -- The two bounds kill every term on the total-degree-q diagonal.
  have hz := P.isZero_rightDerived_comp_of_lt_add Γ hFG F hR hZ q (by omega)
  let E := Sheaf.sectionsFunctorAt X.smallEtaleTopology (i.obj ⊤)
  have e : P ⋙ Γ ≅ E := Iso.refl _
  apply (Sheaf.subsingleton_H_iff_isZero_rightDerived
    X.smallEtaleTopology htop q F).2
  exact hz.of_iso ((NatIso.rightDerived e q).app F).symm

end AlgebraicGeometry.Scheme
