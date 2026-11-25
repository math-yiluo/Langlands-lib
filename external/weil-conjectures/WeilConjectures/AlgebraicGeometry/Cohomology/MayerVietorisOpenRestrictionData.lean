/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Cohomology.MayerVietorisFreeComplex
import WeilConjectures.AlgebraicGeometry.Cohomology.InverseImageOpenFreeSheaf
import WeilConjectures.AlgebraicGeometry.Cohomology.OpenImmersionCoefficientUnit
/-! # Restriction data for the cartesian open-subscheme square

Source: Stacks Project, Tags 03DI, 03DJ, 04J0, and Section 01F7.
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {X : Scheme.{u}}

/-- The base change of the inclusion of an open subscheme.
Source: Stacks Project, Tag 04J0; the cartesian open-subscheme square.
(blueprint: lem-pc-open-restriction-data) -/
noncomputable def H.openBaseChangeInclusion (f : X ⟶ Spec (.of R)) (W : X.Opens) :
    baseChangedScheme (S := S) (W.ι ≫ f) ⟶ baseChangedScheme (S := S) f :=
  Limits.pullback.lift (baseChangeFst (S := S) (W.ι ≫ f) ≫ W.ι)
    (baseChangeSnd (S := S) (W.ι ≫ f)) (by
      dsimp [baseChangeFst, baseChangeSnd]
      rw [Category.assoc]
      exact Limits.pullback.condition)

private lemma coefficientUnit_scalar {Y Z : Scheme.{u}} (j : Z ⟶ Y)
    (M : Y.Modules) (a : Γ(Y, ⊤)) :
    (invImage j).map (scalarRep M a).asHom ≫ coefficientUnit j M =
      coefficientUnit j M ≫ (scalarRep ((pullback j).obj M) (j.appTop a)).asHom := by
  apply coeff_naturality
  rw [pushforward_map_smulHom]
  exact smulHom_naturality ((pullbackPushforwardAdjunction j).unit.app M) a

private lemma scalarRep_naturality {Y : Scheme.{u}} {M N : Y.Modules}
    (t : M ⟶ N) (a : Γ(Y, ⊤)) :
    (scalarRep M a).asHom ≫ (SheafOfModules.toSheaf Y.ringCatSheaf).map t =
      (SheafOfModules.toSheaf Y.ringCatSheaf).map t ≫ (scalarRep N a).asHom := by
  change (SheafOfModules.toSheaf Y.ringCatSheaf).map (M.smulHom a) ≫
    (SheafOfModules.toSheaf Y.ringCatSheaf).map t =
      (SheafOfModules.toSheaf Y.ringCatSheaf).map t ≫
        (SheafOfModules.toSheaf Y.ringCatSheaf).map (N.smulHom a)
  rw [← Functor.map_comp, ← Functor.map_comp, smulHom_naturality]

@[reassoc] private lemma coefficientUnit_congr {Y Z : Scheme.{u}} {f g : Z ⟶ Y}
    (h : f = g) (M : Y.Modules) :
    (invImageCongr h).hom.app ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M) ≫
      coefficientUnit g M =
        coefficientUnit f M ≫
          (SheafOfModules.toSheaf Z.ringCatSheaf).map ((pullbackCongr h).hom.app M) := by
  subst g
  simp [invImageCongr, pullbackCongr]


/-- Degree-zero data for restriction, including the cartesian coefficient square.
Source: Stacks Project, Tags 03DI, 03DJ, 04J0, and Section 01F7.
(blueprint: lem-pc-open-restriction-data)

Proof: Restriction along j = W.ι sends the free sheaf represented by W to the
free sheaf represented by the top open of W. This gives e by the Yoneda,
free/forgetful, and sheafification adjunctions. The underlying abelian sheaf of
j^*M is the restriction of the underlying abelian sheaf of M, because j is an
open immersion and its map of structure sheaves is an isomorphism. The
isomorphism d has as hom the abelian adjoint of the module pullback unit.
Its naturality for multiplication by a section gives the R-scalar square.
The base-changed inclusion k is an open immersion. The cartesian identity
k followed by p equals p_W followed by j gives c, the comparison between
the two composite inverse-image functors, by uniqueness of left adjoints to
the same composite direct-image functor. Composition of module pullbacks in
this square, followed by forgetting to abelian sheaves, gives d'. Naturality
for multiplication by sections from Spec S gives its S-scalar square. The
pullback units compose under these pullback comparisons. Taking abelian
adjoints proves the displayed coefficient square; this uses the unit and
counit identities, so the chosen c and d' are coherent. All data here are
sheaf morphisms in degree zero. No Ext equivalence or bijectivity is asserted.
For an empty open these are isomorphisms of zero sheaves; for the top open
they are the usual restriction identities. No flatness is used.
-/
theorem H.openRestrictionData (f : X ⟶ Spec (.of R)) (M : X.Modules) (W : X.Opens) :
    let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
    let G := invImage (baseChangeFst (S := S) f)
    let N := (SheafOfModules.toSheaf (baseChangedScheme (S := S) f).ringCatSheaf).obj
      (baseChangedModule (S := S) f M)
    let φ := coeff (baseChangeFst (S := S) f) (baseChangeUnit (S := S) f M)
    let ρ := (scalarRep M).comp (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
    let τ := (scalarRep (baseChangedModule (S := S) f M)).comp
      (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
    let MW := (pullback W.ι).obj M
    let FW := (SheafOfModules.toSheaf W.toScheme.ringCatSheaf).obj MW
    let GW := invImage (baseChangeFst (S := S) (W.ι ≫ f))
    let NW := (SheafOfModules.toSheaf
      (baseChangedScheme (S := S) (W.ι ≫ f)).ringCatSheaf).obj
      (baseChangedModule (S := S) (W.ι ≫ f) MW)
    let φW := coeff (baseChangeFst (S := S) (W.ι ≫ f))
      (baseChangeUnit (S := S) (W.ι ≫ f) MW)
    let ρW := (scalarRep MW).comp
      (((Scheme.ΓSpecIso (.of R)).inv ≫ (W.ι ≫ f).appTop).hom)
    let τW := (scalarRep (baseChangedModule (S := S) (W.ι ≫ f) MW)).comp
      (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) (W.ι ≫ f)).appTop).hom)
    let J := invImage W.ι
    let J' := invImage (H.openBaseChangeInclusion (S := S) f W)
    ∃ (e : J.obj (H.openFreeSheaf W) ≅ H.openFreeSheaf (⊤ : W.toScheme.Opens))
      (d : J.obj F ≅ FW) (c : G ⋙ J' ≅ J ⋙ GW) (d' : J'.obj N ≅ NW),
      (∀ a, J.map (ρ a).asHom ≫ d.hom = d.hom ≫ (ρW a).asHom) ∧
      (∀ a, J'.map (τ a).asHom ≫ d'.hom = d'.hom ≫ (τW a).asHom) ∧
      J'.map φ ≫ d'.hom = (c.app F).hom ≫ GW.map d.hom ≫ φW := by
  dsimp only
  let j := W.ι
  let p := baseChangeFst (S := S) f
  let q := baseChangeFst (S := S) (W.ι ≫ f)
  let k := H.openBaseChangeInclusion (S := S) f W
  have h : k ≫ p = q ≫ j := by
    exact Limits.pullback.lift_fst _ _ _
  have hs : k ≫ baseChangeSnd (S := S) f = baseChangeSnd (S := S) (W.ι ≫ f) := by
    exact Limits.pullback.lift_snd _ _ _
  let t : (pullback k).obj ((pullback p).obj M) ≅
      (pullback q).obj ((pullback j).obj M) :=
    (pullbackComp k p).app M ≪≫ (pullbackCongr h).app M ≪≫
      ((pullbackComp q j).app M).symm
  let c : invImage p ⋙ invImage k ≅ invImage j ⋙ invImage q :=
    invImageComp k p ≪≫ invImageCongr h ≪≫ (invImageComp q j).symm
  have : IsOpenImmersion k := by
    change IsOpenImmersion (Limits.pullback.map (W.ι ≫ f) (baseChangeMap R S)
      f (baseChangeMap R S) W.ι (𝟙 _) (𝟙 _) (by simp) (by simp))
    infer_instance
  have := coefficientUnit_isIso_of_isOpenImmersion j M
  have := coefficientUnit_isIso_of_isOpenImmersion k ((pullback p).obj M)
  let d := asIso (coefficientUnit j M)
  let d' := asIso (coefficientUnit k ((pullback p).obj M)) ≪≫
    (SheafOfModules.toSheaf _).mapIso t
  obtain ⟨e⟩ := H.invImage_openFreeSheaf_iso j W
  have he : j ⁻¹ᵁ W = ⊤ := by
    ext x
    simp [j]
  refine ⟨e ≪≫ eqToIso (congrArg H.openFreeSheaf he),
    d, c, d', ?_, ?_, ?_⟩
  · intro a
    change (invImage j).map (scalarRep M _).asHom ≫ coefficientUnit j M =
      coefficientUnit j M ≫ (scalarRep ((pullback j).obj M) _).asHom
    rw [Scheme.Hom.comp_appTop]
    exact coefficientUnit_scalar j M _
  · intro a
    change (invImage k).map (scalarRep ((pullback p).obj M) _).asHom ≫
      (coefficientUnit k ((pullback p).obj M) ≫
        (SheafOfModules.toSheaf _).map t.hom) =
      (coefficientUnit k ((pullback p).obj M) ≫
        (SheafOfModules.toSheaf _).map t.hom) ≫
          (scalarRep ((pullback q).obj ((pullback j).obj M)) _).asHom
    rw [← Category.assoc, coefficientUnit_scalar, Category.assoc, scalarRep_naturality]
    have hh := congrArg Scheme.Hom.appTop hs
    rw [Scheme.Hom.comp_appTop] at hh
    have ha := ConcreteCategory.congr_hom (congrArg
      (fun v ↦ (Scheme.ΓSpecIso (.of S)).inv ≫ v) hh) a
    change k.appTop (((Scheme.ΓSpecIso (.of S)).inv ≫
      (baseChangeSnd (S := S) f).appTop).hom a) = _ at ha
    simp only [ha, Category.assoc]
  · change (invImage k).map (coefficientUnit p M) ≫
        (coefficientUnit k ((pullback p).obj M) ≫
          (SheafOfModules.toSheaf _).map t.hom) =
      c.hom.app ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) ≫
        (invImage q).map (coefficientUnit j M) ≫
          coefficientUnit q ((pullback j).obj M)
    dsimp only [c, t]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      NatTrans.comp_app, Functor.map_comp, Category.assoc]
    rw [coefficientUnit_comp_assoc]
    rw [← coefficientUnit_congr_assoc h M]
    congr 1
    congr 1
    apply (cancel_epi ((invImageComp q j).hom.app
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))).mp
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    rw [← coefficientUnit_comp]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    simp only [Functor.comp_obj]
    simp

end AlgebraicGeometry.Scheme.Modules
