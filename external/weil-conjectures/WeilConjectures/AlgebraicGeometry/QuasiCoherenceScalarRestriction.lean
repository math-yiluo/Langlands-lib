/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.AffineAlgebraModulePresentation
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Quasi-coherence and restriction of scalars

Source: Stacks Project, Morphisms, Lemma 0H88; EGA I, Proposition 9.6.1
(blueprint: lem-weil-pbc-quasi-coherence-scalar-restriction).

The quasi-coherent `𝒪_S`-algebra is the shared form `A : S.CommAlgebraSheaf`
(`= Under S.sheaf`, def-weil-pbc-comm-algebra-sheaf) with `A.toModule.IsQuasicoherent`;
`A`-modules are `SheafOfModules` over
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj A.right` and their underlying
`𝒪_S`-modules are obtained by scalar restriction along `A.hom`, as in
`lem-weil-pbc-quasi-coherent-algebra-change-of-rings`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private theorem restrictScalars_preservesColimits
    {C : Type u} [Category C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    PreservesColimitsOfSize.{u, u} (SheafOfModules.restrictScalars.{u} α) := by
  have h (B : Sheaf J RingCat.{u}) :
      PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} B) := by
    constructor
    intro K _
    exact ((moduleSheaves_colimits_forgetful B).2.2.2.2.2 K).2.1
  have := h R
  have := h R'
  have : ReflectsColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} R) :=
    reflectsColimits_of_reflectsIsomorphisms
  have : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.restrictScalars.{u} α ⋙ SheafOfModules.toSheaf.{u} R) :=
    inferInstanceAs (PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} R'))
  exact preservesColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{u} R)

private theorem quasiCoherent_map_presentation
    {C : Type u} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {X : Scheme.{u}} (F : SheafOfModules.{u} R ⥤ X.Modules)
    [F.Additive] [PreservesColimitsOfSize.{u, u} F]
    (hF : (F.obj (SheafOfModules.unit R)).IsQuasicoherent)
    {M : SheafOfModules.{u} R} (p : M.Presentation) :
    (F.obj M).IsQuasicoherent := by
  have hfree (I : Type u) : (F.obj (SheafOfModules.free (R := R) I)).IsQuasicoherent := by
    have : ∀ i : I, (F.obj (SheafOfModules.unit R)).IsQuasicoherent := fun _ ↦ hF
    have := isQuasicoherent_sigma (fun _ : I ↦ F.obj (SheafOfModules.unit R))
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (PreservesCoproduct.iso F (fun _ : I ↦ SheafOfModules.unit R)).symm inferInstance
  let f := (SheafOfModules.freeHomEquiv _).symm p.relations.s ≫ kernel.ι p.generators.π
  have := hfree p.relations.I
  have := hfree p.generators.I
  have := isQuasicoherent_cokernel (F.map f)
  let e₀ : cokernel f ≅ M :=
    (p.isColimit.coconePointUniqueUpToIso (colimit.isColimit _)).symm
  let e : cokernel (F.map f) ≅ F.obj M :=
    (PreservesCokernel.iso F f).symm ≪≫ F.mapIso e₀
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e inferInstance

set_option backward.isDefEq.respectTransparency false in
private theorem quasiCoherent_overEquiv_inverse {S : Scheme.{u}} (U : S.Opens)
    (M : U.toScheme.Modules) [M.IsQuasicoherent] :
    ((overEquiv U).inverse.obj M).IsQuasicoherent := by
  have := U.instIsDenseSubsiteSubtypeMemOverGrothendieckTopologyOverInverseOverEquivalence
  have (V : Over U) :
      (Over.post U.overEquivalence.functor).IsContinuous
        (((Opens.grothendieckTopology S).over U).over V)
        ((Opens.grothendieckTopology U.carrier).over (U.overEquivalence.functor.obj V)) := by
    exact Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous U.overEquivalence.functor _ _).overPost V)
  apply SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
    U.overEquivalence.functor _ (U.sheafOfModulesEquivOverInverseUnit S.ringCatSheaf)

private theorem quasiCoherent_over_of_equiv {S : Scheme.{u}} (U : S.Opens)
    (M : S.Modules) (h : ((overEquiv U).functor.obj (M.over U)).IsQuasicoherent) :
    (M.over U).IsQuasicoherent := by
  have := h
  exact (SheafOfModules.isQuasicoherent (S.ringCatSheaf.over U)).prop_of_iso
    ((overEquiv U).unitIso.app (M.over U)).symm
    (quasiCoherent_overEquiv_inverse U ((overEquiv U).functor.obj (M.over U)))

set_option backward.isDefEq.respectTransparency false in
private theorem quasiCoherent_restrictScalars (S : Scheme.{u})
    (A : S.CommAlgebraSheaf) (hA : A.toModule.IsQuasicoherent)
    (G : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).obj
        A.right)) (hG : G.IsQuasicoherent) :
    ((SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).map
        A.hom)).obj G).IsQuasicoherent := by
  have := hA
  have := hG
  obtain ⟨q⟩ := SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := G)
  let ρ := SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).map A.hom)
  have hlocal (i : q.I) : ((ρ.obj G).over (q.X i)).IsQuasicoherent := by
    let U : S.Opens := q.X i
    let α := ((Over.forget U).sheafPushforwardContinuous RingCat
      ((Opens.grothendieckTopology S).over U) (Opens.grothendieckTopology S)).map
      ((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).map A.hom)
    have := restrictScalars_preservesColimits α
    let F := SheafOfModules.restrictScalars α ⋙ (overEquiv U).functor
    have : (overEquiv U).functor.Additive :=
      Functor.additive_of_preserves_binary_products _
    have hunit : (F.obj (SheafOfModules.unit _)).IsQuasicoherent := by
      change ((overEquiv U).functor.obj (A.toModule.over U)).IsQuasicoherent
      exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
        ((overFunctorEquiv U).app A.toModule).symm inferInstance
    apply quasiCoherent_over_of_equiv U (ρ.obj G)
    exact quasiCoherent_map_presentation F hunit (q.presentation i)
  exact SheafOfModules.IsQuasicoherent.of_coversTop (ρ.obj G) q.X q.coversTop

/-- For a quasi-coherent commutative algebra sheaf on a scheme, an algebra-module sheaf
is quasi-coherent exactly when its underlying structure-sheaf module is quasi-coherent.
The algebra is `A : S.CommAlgebraSheaf` with structure map `A.hom`; the hypothesis `hA`
requires its underlying module `A.toModule` to be quasi-coherent. Mathlib's
`IsQuasicoherent` is the local
presentation by arbitrary direct sums of copies of the ring sheaf (Stacks 01BE),
equivalent on schemes to the affine-local tilde condition of `pqf-def-coherent` (01IA).

Source: Stacks Project, Morphisms, Lemma 0H88; EGA I, Proposition 9.6.1
(blueprint: lem-weil-pbc-quasi-coherence-scalar-restriction).

Proof, following the six steps of the node:
1. Forgetting algebra scalars preserves direct sums and exact sequences, since both
module categories have exact forgetful functors to abelian sheaves preserving colimits
(`situation-conventions`).
2. On an affine open `U = Spec R`, put `B = A(U)`. The tilde-Gamma adjunction identifies
the underlying module of each direct sum of copies of `A|U` with the tilde of the
corresponding direct sum of copies of `B`. Thus these sums are quasi-coherent, using
`lem-weil-pbc-module-restriction-open-immersion-colimits` and
`lem-weil-pbc-affine-tilde-gamma-adjunction`.
3. A local algebra-module presentation is therefore a presentation by quasi-coherent
structure-sheaf modules. Its cokernel is quasi-coherent by
`lem-weil-pbc-quasi-coherent-module-cokernel-image`, giving the forward implication.
4. Conversely, on an affine open put `M = G(U)`, a `B`-module by its sectionwise action.
Its restricted `R`-action agrees with the structure-sheaf action. Present `M` by free
`B`-modules, taking all elements as generators and all kernel elements as relations.
5. Define the maps between direct sums of `A|U` and `G|U` from these sections. They are
`A|U`-linear by compatibility of the action with restriction
(`situation-conventions`).
6. Under the tilde-Gamma identifications the maps are the tildes of the free presentation.
The tilde functor preserves cokernels and direct sums, so the sequence is exact as a
structure-sheaf sequence, hence also as an algebra-module sequence by step 1. These
affine presentations give algebra-module quasi-coherence, proving the converse. -/
theorem quasiCoherent_iff_restrictScalars (S : Scheme.{u})
    (A : S.CommAlgebraSheaf) (hA : A.toModule.IsQuasicoherent)
    (G : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).obj
        A.right)) :
    G.IsQuasicoherent ↔
      ((SheafOfModules.restrictScalars
        ((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).map
          A.hom)).obj G).IsQuasicoherent := by
  constructor
  · exact quasiCoherent_restrictScalars S A hA G
  · intro hG
    have := hG
    classical
    let U : S.affineOpens → S.Opens := fun V ↦ V.1
    have hcover : (Opens.grothendieckTopology S).CoversTop U := by
      apply (Opens.coversTop_iff _ U).mpr
      change (⨆ V : S.affineOpens, V.1) = ⊤
      refine eq_top_iff.mpr fun x _ ↦ ?_
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
        S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hxV⟩
    have hlocal (V : S.affineOpens) : (G.over (U V)).IsQuasicoherent := by
      obtain ⟨p⟩ := nonempty_algebraModule_presentation_over S A hA G V.1 V.2
        (SheafOfModules.isQuasicoherent_over
          ((SheafOfModules.restrictScalars
            ((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).map
              A.hom)).obj G) V.1)
      exact p.isQuasicoherent
    exact SheafOfModules.IsQuasicoherent.of_coversTop G U hcover

end AlgebraicGeometry.Scheme.Modules
