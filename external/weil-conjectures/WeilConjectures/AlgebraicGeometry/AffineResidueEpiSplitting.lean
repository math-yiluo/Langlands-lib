/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback
import WeilConjectures.Algebra.Homology.ModuleStalkFunctor

/-! # Splitting an affine module map detected on residue fibres

Source: Stacks Project, Tags 056J and 00NX, the finite-cokernel support
argument and finite-projective splitting.
(blueprint: lem-pc-affine-residue-epi-splitting)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- An epimorphic image of a finite-type module is finite type: compose each local finite
family of generating sections with the epimorphism. Source: Stacks Project, Tag 01B7. -/
private theorem finiteType_of_epi {X : Scheme.{u}} {P Q : X.Modules}
    (a : P ⟶ Q) [Epi a] [P.IsFiniteType] : Q.IsFiniteType := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData P
  let q' : Q.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi (a.over (q.X i)) }
  have : q'.IsFiniteType := by
    refine SheafOfModules.LocalGeneratorsData.IsFiniteType.mk (p := q') (fun i ↦ ?_)
    have := hq.isFiniteType i
    exact inferInstanceAs ((q.generators i).ofEpi _).IsFiniteType
  apply SheafOfModules.IsFiniteType.mk (R := X.ringCatSheaf)
  exact ⟨q', this⟩

set_option backward.isDefEq.respectTransparency false in
/-- Residue pullbacks detect epimorphisms into finite-type quasi-coherent modules.
The cokernel is quasi-coherent and finite type. Its pullback to each residue field is
zero, so the support-pullback equality of Stacks Tag 056J makes its support empty.
Stalkwise sheaf separation then makes the cokernel zero. -/
private theorem epi_of_residue_epi {X : Scheme.{u}} {P Q : X.Modules}
    (a : P ⟶ Q) [P.IsQuasicoherent] [Q.IsQuasicoherent] [Q.IsFiniteType]
    (ha : ∀ x : X, Epi ((pullback (X.fromSpecResidueField x)).map a)) : Epi a := by
  classical
  let C := cokernel a
  have : C.IsQuasicoherent := isQuasicoherent_cokernel a
  have : C.IsFiniteType := finiteType_of_epi (cokernel.π a)
  have hs := (finiteType_module_support_pullback C).2.2
  have hstalk (x : X) : Subsingleton (C.presheaf.stalk x) := by
    let i := X.fromSpecResidueField x
    obtain ⟨adj⟩ := nonempty_tensorPullbackAdjunction i
    let e : tensorPullback i ≅ pullback i :=
      adj.leftAdjointUniq (pullbackPushforwardAdjunction i)
    have : Epi ((pullback i).map a) := ha x
    have hepi : Epi ((tensorPullback i).map a) := by
      have hnat : (tensorPullback i).map a ≫ e.hom.app Q =
          e.hom.app P ≫ (pullback i).map a := e.hom.naturality a
      have : Epi (e.hom.app P ≫ (pullback i).map a) := inferInstance
      rw [← hnat] at this
      exact (epi_comp_iff_of_isIso _ (e.hom.app Q)).mp this
    have : (tensorPullback i).IsLeftAdjoint := adj.isLeftAdjoint
    have hzero : IsZero ((tensorPullback i).obj C) :=
      (isZero_cokernel_of_epi ((tensorPullback i).map a)).of_iso
        (PreservesCokernel.iso (tensorPullback i) a)
    let y : Spec (X.residueField x) := IsLocalRing.closedPoint _
    have hy : Subsingleton (((tensorPullback i).obj C).presheaf.stalk y) :=
      ModuleCat.subsingleton_of_isZero
        ((RingedSpace.moduleStalkFunctor _ y).map_isZero hzero)
    have hsupport := (hs _ i).2
    have hx : i y = x := by simp [i, Scheme.fromSpecResidueField_apply]
    by_contra h
    have hm : y ∈ i.base ⁻¹' {z : X | ¬ Subsingleton (C.presheaf.stalk z)} := by
      change ¬ Subsingleton (C.presheaf.stalk (i y))
      rwa [hx]
    rw [← hsupport] at hm
    exact hm hy
  have hzero : IsZero C := by
    apply (IsZero.iff_id_eq_zero C).mpr
    apply hom_ext
    intro U
    ext t
    change t = 0
    apply TopCat.Presheaf.section_ext (⟨C.presheaf, C.isSheaf⟩ : TopCat.Sheaf Ab X)
    intro x hx
    exact @Subsingleton.elim _ (hstalk x) _ _
  exact Abelian.epi_of_cokernel_π_eq_zero a (hzero.eq_of_tgt _ _)

set_option backward.isDefEq.respectTransparency false in
/-- Residue surjectivity splits a map onto a finitely presented flat affine module.

Source: Stacks Project, Tags 056J and 00NX; finite-cokernel Nakayama argument.
(blueprint: lem-pc-affine-residue-epi-splitting).

Proof: The quasi-coherent cokernel of f is finite type, since it is an epimorphic
image of the finite-presentation target. Pullback preserves cokernels, and all residue
pullbacks of f are epimorphisms, so all residue pullbacks of its cokernel vanish.
The support-pullback equality of 056J makes every cokernel stalk zero. Sheaf separation
makes the cokernel zero and f an epimorphism. This step needs no flatness or affine-ness.
Now identify S with Spec A, where A = Γ(S, ⊤), and restrict M, N and f to Spec A.
The quasi-coherent counit isomorphisms and full faithfulness of tilde show that the
section map is an epimorphism. Finite presentation of N gives finite presentation of
its affine sections, and IsFlatOver evaluated at the top affine open gives flatness.
Thus these sections are projective by 00NX. Transport projectivity through the affine
section identification and use Projective.factorThru to split the section map.
Apply tilde and conjugate by the counit isomorphisms to split the restricted sheaf map.
Finally transport the section back along the inverse affine isomorphism. Naturality
of the counit and of the restriction-composition isomorphism proves both right-inverse
identities. No finiteness of M is needed. The empty scheme case follows from the same
argument: the stalk conditions are vacuous and sheaf separation gives zero modules. -/
theorem affine_isSplitEpi_of_residue_epi (S : Scheme.{u}) (hS : IsAffine S)
    (M N : S.Modules) (f : M ⟶ N)
    (hMqc : M.IsQuasicoherent) (hNqc : N.IsQuasicoherent)
    (hNflat : N.IsFlatOver (𝟙 S)) (hNfp : N.IsFinitePresentation)
    (hf : ∀ s : S, Epi ((Modules.pullback (S.fromSpecResidueField s)).map f)) :
    IsSplitEpi f := by
  have : IsAffine S := hS
  have : M.IsQuasicoherent := hMqc
  have : N.IsQuasicoherent := hNqc
  have : N.IsFinitePresentation := hNfp
  have : Epi f := epi_of_residue_epi f hf
  let U : S.Opens := ⊤
  let hU : IsAffineOpen U := isAffineOpen_top S
  let j := hU.fromSpec
  let F := restrictFunctor j
  let M' := F.obj M
  let N' := F.obj N
  let f' := F.map f
  have : Epi f' := inferInstance
  have : M'.IsQuasicoherent := inferInstance
  have : N'.IsQuasicoherent := inferInstance
  have : IsIso M'.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent M'
  have : IsIso N'.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent N'
  have hfp : Module.FinitePresentation Γ(S, U) Γ(N, U) :=
    finitePresentation_sections_of_isFinitePresentation N hU
  have hflat := hNflat ⟨U, hU⟩ ⟨U, hU⟩ (by simp)
  have hid : (𝟙 S : S ⟶ S).appLE U U (by simp) = 𝟙 Γ(S, U) := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, homOfLE_refl,
      op_id, Category.id_comp]
    exact S.presheaf.map_id _
  change @Module.Flat Γ(S, U) Γ(N, U) _ _
    (Module.compHom Γ(N, U) ((𝟙 S : S ⟶ S).appLE U U (by simp)).hom) at hflat
  rw [hid] at hflat
  have : Module.Flat Γ(S, U) Γ(N, U) := hflat
  have : Module.Projective Γ(S, U) Γ(N, U) :=
    Module.Flat.projective_of_finitePresentation
  let e := sectionsRestrictFromSpecLinearEquiv N hU
  have : Module.Projective Γ(S, U) (moduleSpecΓFunctor.obj N') :=
    Module.Projective.of_equiv e.symm
  let g := moduleSpecΓFunctor.map f'
  have hg : Epi ((tilde.functor Γ(S, U)).map g) := by
    have hnat : (tilde.functor Γ(S, U)).map g ≫ N'.fromTildeΓ =
        M'.fromTildeΓ ≫ f' := fromTildeΓNatTrans.naturality f'
    have : Epi (M'.fromTildeΓ ≫ f') := inferInstance
    rw [← hnat] at this
    exact (epi_comp_iff_of_isIso _ N'.fromTildeΓ).mp this
  have : Epi g := (tilde.functor Γ(S, U)).epi_of_epi_map hg
  let r := Projective.factorThru (𝟙 (moduleSpecΓFunctor.obj N')) g
  have hr : r ≫ g = 𝟙 _ := Projective.factorThru_comp _ _
  let r' : N' ⟶ M' :=
    inv N'.fromTildeΓ ≫ (tilde.functor Γ(S, U)).map r ≫ M'.fromTildeΓ
  have hr' : r' ≫ f' = 𝟙 N' := by
    dsimp only [r']
    have hnat : (tilde.functor Γ(S, U)).map g ≫ N'.fromTildeΓ =
        M'.fromTildeΓ ≫ f' := fromTildeΓNatTrans.naturality f'
    rw [Category.assoc, Category.assoc, ← hnat]
    rw [← Category.assoc ((tilde.functor Γ(S, U)).map r), ← Functor.map_comp, hr]
    rw [CategoryTheory.Functor.map_id, Category.id_comp, IsIso.inv_hom_id]
  have hj : IsIso j := by
    dsimp only [j, hU, U]
    rw [IsAffineOpen.fromSpec_top]
    infer_instance
  let G := restrictFunctor (inv j)
  let η : F ⋙ G ≅ 𝟭 S.Modules :=
    (restrictFunctorComp (inv j) j).symm ≪≫
      restrictFunctorCongr (IsIso.inv_hom_id j) ≪≫ restrictFunctorId
  refine ⟨⟨η.inv.app N ≫ G.map r' ≫ η.hom.app M, ?_⟩⟩
  have hnat : G.map f' ≫ η.hom.app N = η.hom.app M ≫ f := η.hom.naturality f
  rw [Category.assoc, Category.assoc, ← hnat]
  rw [← Category.assoc (G.map r'), ← G.map_comp, hr', G.map_id]
  simp

end AlgebraicGeometry.Scheme.Modules
