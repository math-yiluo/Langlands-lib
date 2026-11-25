/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FpqcFullyFaithful
public import WeilConjectures.AlgebraicGeometry.Modules.HomSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Sections of quasi-coherent modules form an fpqc sheaf

For a quasi-coherent module `N` on a scheme `X`, the presheaf `(y : Y ⟶ X) ↦ Γ(y^* N, ⊤)` on
schemes over `X` is a sheaf for the fpqc topology. We state this for sections over an open `O`
of `X` and a sieve on `X` whose restriction to `O` is an fpqc covering.

The proof identifies sections of `y^* N` with morphisms `y^* 𝒪_X ⟶ y^* N`
(`AlgebraicGeometry.Scheme.Modules.homSection`) and uses the fpqc sheaf property of the
presheaf of morphisms (`AlgebraicGeometry.isSheaf_presheafHom`).
-/

@[expose] public section

universe u

open CategoryTheory Opposite CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
lemma isSheafFor_presheafHom_of_mem_fpqcTopology {S : Scheme.{u}}
    (M N : modulesPseudofunctor.obj (.mk (op S)))
    (hM : (M : S.Modules).IsQuasicoherent) (hN : (N : S.Modules).IsQuasicoherent)
    (R : Sieve S) (hR : R ∈ Scheme.fpqcTopology S) :
    Presieve.IsSheafFor (modulesPseudofunctor.presheafHom M N)
      ((Sieve.overEquiv (Over.mk (𝟙 S))).symm R).arrows := by
  have h := bijective_toDescentData_map_of_mem_fpqcTopology
    (fun (i : R.arrows.category) ↦ i.obj.hom)
    (by rwa [Sieve.ofArrows_category', Sieve.generate_sieve]) M N hM hN
  rw [Pseudofunctor.bijective_toDescentData_map_iff] at h
  convert! h
  refine le_antisymm ?_ ?_
  · rintro X f (hf : R.arrows f.left)
    obtain ⟨X, g, rfl⟩ := Over.mk_surjective X
    obtain rfl : f = Over.homMk g := by ext; simpa using Over.w f
    exact Presieve.ofArrows.mk (ι := R.arrows.category) ⟨Over.mk g, hf⟩
  · rintro _ _ ⟨_, h⟩
    exact h

set_option backward.isDefEq.respectTransparency false in
lemma isSheafFor_presheafHom_of_mem_over {S₀ : Scheme.{u}}
    (M N : modulesPseudofunctor.obj (.mk (op S₀)))
    (hM : (M : S₀.Modules).IsQuasicoherent) (hN : (N : S₀.Modules).IsQuasicoherent)
    {U : Over S₀} (R : Sieve U) (hR : R ∈ (Scheme.fpqcTopology.over S₀) U) :
    Presieve.IsSheafFor (modulesPseudofunctor.presheafHom M N) R.arrows := by
  obtain ⟨S, a, rfl⟩ := U.mk_surjective
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨R, rfl⟩ := (Sieve.overEquiv (Over.mk a)).symm.surjective R
  rw [OrderIso.apply_symm_apply] at hR
  have h := isSheafFor_presheafHom_of_mem_fpqcTopology
    ((modulesPseudofunctor.map a.op.toLoc).toFunctor.obj M)
    ((modulesPseudofunctor.map a.op.toLoc).toFunctor.obj N)
    (Scheme.Modules.isQuasicoherent_pullback (M := (M : S₀.Modules)) a)
    (Scheme.Modules.isQuasicoherent_pullback (M := (N : S₀.Modules)) a) _ hR
  rw [← Presieve.isSheafFor_iff_of_iso (modulesPseudofunctor.overMapCompPresheafHomIso M N a),
    Presieve.isSheafFor_over_map_op_comp_iff (X' := Over.mk a)
      (e := Over.isoMk (Iso.refl _))] at h
  convert! h
  refine le_antisymm ?_ ?_
  · intro Y f hf
    exact ⟨Over.mk f.left, Over.homMk f.left, Over.homMk (𝟙 _) (by simpa using Over.w f),
      hf, by cat_disch⟩
  · rintro X b ⟨Y, c, d, h, fac⟩
    replace fac := (Over.forget _).congr_map fac
    change b.left ≫ 𝟙 _ = _ at fac
    rw [Category.comp_id] at fac
    change R.arrows b.left
    simpa [fac] using R.downward_closed h d.left

/-- For quasi-coherent `M` and `N` on `S`, the presheaf `Hom(- ^* M, - ^* N)` on schemes over `S`
is a sheaf for the fpqc topology. -/
lemma isSheaf_presheafHom {S : Scheme.{u}} (M N : modulesPseudofunctor.obj (.mk (op S)))
    (hM : (M : S.Modules).IsQuasicoherent) (hN : (N : S.Modules).IsQuasicoherent) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (modulesPseudofunctor.presheafHom M N) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro U R hR
  exact isSheafFor_presheafHom_of_mem_over M N hM hN R hR

/-- The restriction maps of `Pseudofunctor.presheafHom` are given by `pullHom`. -/
lemma _root_.CategoryTheory.Pseudofunctor.presheafHom_map_eq_pullHom {C : Type*} [Category* C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat} {S : C} {M N : F.obj (.mk (op S))}
    {T T' : Over S} (g : T' ⟶ T) (φ : (F.presheafHom M N).obj (op T)) :
    (F.presheafHom M N).map g.op φ = pullHom φ g.left T'.hom T'.hom (Over.w g) (Over.w g) :=
  rfl

namespace Scheme.Modules

section HomSectionAt

variable {X Y Z : Scheme.{u}}

/-- `homSection f` is surjective: a section `s` of `f^* A` is attached to
`f^* 𝒪 ≅ 𝒪 ⟶ f^* A`, `r ↦ r • s`. -/
lemma homSection_surjective (f : Y ⟶ X) {A : X.Modules} :
    Function.Surjective (homSection f (A := A)) := by
  intro s
  refine ⟨(pullbackObjUnitIso f).hom ≫ homOfGlobalSection _ s, ?_⟩
  have k : (pullbackObjUnitIso f).hom.app ⊤
      ((pullbackObjUnitIso f).inv.app ⊤ (1 : Γ(Y, ⊤))) = (1 : Γ(Y, ⊤)) := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.inv_hom_id, Hom.id_app]
    rfl
  rw [homSection, pullbackSection_one_eq, Hom.comp_app, ConcreteCategory.comp_apply]
  erw [k, homOfGlobalSection_app_one]
  exact presheaf_map_id_apply _ _

/-- The section `φ(f^* 1)` of `f^* A` over `f⁻¹ U` attached to `φ : f^* 𝒪 ⟶ f^* A`. -/
noncomputable def homSectionAt (f : Y ⟶ X) {A : X.Modules} (U : X.Opens)
    (φ : (pullback f).obj (unit X) ⟶ (pullback f).obj A) : Γ((pullback f).obj A, f ⁻¹ᵁ U) :=
  φ.app (f ⁻¹ᵁ U) (pullbackUnitApp f (unit X) U (1 : Γ(X, U)))

/-- `homSectionAt f U φ` is the restriction of `homSection f φ`. -/
lemma homSectionAt_eq (f : Y ⟶ X) {A : X.Modules} (U : X.Opens)
    (φ : (pullback f).obj (unit X) ⟶ (pullback f).obj A) :
    homSectionAt f U φ = ((pullback f).obj A).presheaf.map
      (homOfLE (f.preimage_mono (le_top : U ≤ ⊤))).op (homSection f φ) := by
  rw [homSection, ← Hom.app_presheaf_map, homSectionAt,
    ← pullbackSection_map _ (le_top (a := U))]
  exact congrArg _ (congrArg _ (map_one (X.presheaf.map (homOfLE (le_top (a := U))).op).hom).symm)

/-- If `f⁻¹ U = ⊤`, then `homSectionAt f U` is bijective. -/
lemma bijective_homSectionAt (f : Y ⟶ X) {A : X.Modules} {U : X.Opens} (hU : f ⁻¹ᵁ U = ⊤) :
    Function.Bijective (homSectionAt f U (A := A)) := by
  have : IsIso (homOfLE (f.preimage_mono (le_top : U ≤ ⊤))) :=
    ⟨homOfLE (by rw [hU]; exact le_top), Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have e : homSectionAt f U (A := A) = ((pullback f).obj A).presheaf.map
      (homOfLE (f.preimage_mono (le_top : U ≤ ⊤))).op ∘ homSection f :=
    funext (homSectionAt_eq f U)
  rw [e]
  exact (ConcreteCategory.bijective_of_isIso _).comp
    ⟨homSection_injective f, homSection_surjective f⟩

/-- Restriction of `homSectionAt` along `g`. -/
lemma homSectionAt_comp (f : Y ⟶ X) (g : Z ⟶ Y) {A : X.Modules} (U : X.Opens)
    (φ : (pullback f).obj (unit X) ⟶ (pullback f).obj A) :
    homSectionAt (g ≫ f) U ((pullbackComp g f).inv.app _ ≫ (pullback g).map φ ≫
        (pullbackComp g f).hom.app A) =
      ((pullbackComp g f).hom.app A).app _
        (pullbackUnitApp g _ (f ⁻¹ᵁ U) (homSectionAt f U φ)) := by
  have h1 := pullbackSection_pullbackSection g f (M := unit X) (1 : Γ(X, U))
  have h2 := congrArg (fun ψ ↦ Hom.app ψ (f ⁻¹ᵁ U)
    (pullbackSection f (M := unit X) (1 : Γ(X, U))))
    ((pullbackPushforwardAdjunction g).unit.naturality φ)
  simp only [Functor.id_map, Functor.comp_map, Hom.comp_app, pushforward_map_app,
    ConcreteCategory.comp_apply] at h2
  simp only [homSectionAt, Hom.comp_app, ConcreteCategory.comp_apply]
  erw [← h1]
  exact congrArg _ h2.symm

set_option backward.isDefEq.respectTransparency.types false in
/-- If the section attached to `φ` is the pullback of `s`, then so is the section attached to the
restriction of `φ` along `g`. -/
lemma homSectionAt_pullHom_of_eq (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X) (h : g ≫ f = gf)
    {A : modulesPseudofunctor.obj (.mk (op X))} {U : X.Opens} (s : Γ((A : X.Modules), U))
    (φ : (modulesPseudofunctor.map f.op.toLoc).toFunctor.obj (unit X : X.Modules) ⟶
      (modulesPseudofunctor.map f.op.toLoc).toFunctor.obj A)
    (hφ : homSectionAt f U φ = pullbackUnitApp f A U s) :
    homSectionAt gf U (pullHom (F := modulesPseudofunctor) φ g gf gf h h) =
      pullbackUnitApp gf A U s := by
  subst h
  rw [pullHom_eq_pullbackComp, homSectionAt_comp, hφ]
  refine (congrArg (((pullbackComp g f).hom.app (A : X.Modules)).app _)
    (pullbackUnit_comp_app_apply g f (A : X.Modules) U s).symm).trans ?_
  exact congr(Hom.app $((pullbackComp g f).inv_hom_id_app (A : X.Modules)) _
    (pullbackUnitApp (g ≫ f) _ U s))

set_option backward.isDefEq.respectTransparency.types false in
/-- If the section attached to `φ` is `x f`, for a family `x` of sections compatible with
pullbacks, then the section attached to the restriction of `φ` along `g` is `x (g ≫ f)`. -/
lemma homSectionAt_pullHom_of_eq_family {A : modulesPseudofunctor.obj (.mk (op X))}
    {U : X.Opens} (R : Sieve X)
    (x : ∀ ⦃Z : Scheme.{u}⦄ (y : Z ⟶ X), R y → Γ((pullback y).obj (A : X.Modules), y ⁻¹ᵁ U))
    (hx : ∀ ⦃Z Z' : Scheme.{u}⦄ (y : Z ⟶ X) (hy : R y) (g : Z' ⟶ Z),
      x (g ≫ y) (R.downward_closed hy g) =
        ((pullbackComp g y).hom.app _).app _ (pullbackUnitApp g _ (y ⁻¹ᵁ U) (x y hy)))
    (f : Y ⟶ X) (hf : R f) (g : Z ⟶ Y) (gf : Z ⟶ X) (h : g ≫ f = gf) (hgf : R gf)
    (φ : (modulesPseudofunctor.map f.op.toLoc).toFunctor.obj (unit X : X.Modules) ⟶
      (modulesPseudofunctor.map f.op.toLoc).toFunctor.obj A)
    (hφ : homSectionAt f U φ = x f hf) :
    homSectionAt gf U (pullHom (F := modulesPseudofunctor) φ g gf gf h h) = x gf hgf := by
  subst h
  rw [pullHom_eq_pullbackComp, homSectionAt_comp, hφ, hx]

end HomSectionAt

variable {X : Scheme.{u}}

/-- **Sections of a quasi-coherent module are separated for the fpqc topology.** Two sections
of `N` over `O` agree if their pullbacks along all members of a sieve which restricts to an fpqc
covering of `O` agree. -/
theorem sections_ext_of_mem_fpqcTopology (N : X.Modules) [N.IsQuasicoherent] {O : X.Opens}
    (R : Sieve X) (hR : Sieve.pullback O.ι R ∈ Scheme.fpqcTopology O.toScheme)
    {s t : Γ(N, O)}
    (h : ∀ ⦃Z : Scheme.{u}⦄ (y : Z ⟶ X), R y →
      pullbackUnitApp y N O s = pullbackUnitApp y N O t) : s = t := by
  have hsep := (isSheafFor_presheafHom_of_mem_over (unit X) N
    (SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)) inferInstance _
    (GrothendieckTopology.overEquiv_symm_mem_over _ (Over.mk O.ι) _ hR)).isSeparatedFor
  obtain ⟨φ, hφ⟩ := (bijective_homSectionAt O.ι (A := N) O.ι_preimage_self).2
    (pullbackUnitApp O.ι N O s)
  obtain ⟨ψ, hψ⟩ := (bijective_homSectionAt O.ι (A := N) O.ι_preimage_self).2
    (pullbackUnitApp O.ι N O t)
  have key : φ = ψ := by
    refine hsep.ext (fun V g hg ↦ ?_)
    have hV : V.hom ⁻¹ᵁ O = ⊤ := by
      rw [← Over.w g, Scheme.Hom.comp_preimage]
      exact congrArg (g.left ⁻¹ᵁ ·) O.ι_preimage_self
    apply (bijective_homSectionAt V.hom (A := N) hV).1
    rw [Pseudofunctor.presheafHom_map_eq_pullHom, Pseudofunctor.presheafHom_map_eq_pullHom,
      homSectionAt_pullHom_of_eq O.ι g.left V.hom (Over.w g) s φ hφ,
      homSectionAt_pullHom_of_eq O.ι g.left V.hom (Over.w g) t ψ hψ]
    refine h _ ?_
    rw [← Over.w g]
    exact hg
  apply (bijective_pullbackUnit_app_of_isOpenImmersion O.ι N O.opensRange_ι.ge).1
  rw [← key] at hψ
  exact hφ.symm.trans hψ

/-- **Sections of a quasi-coherent module glue for the fpqc topology.** A family of sections of
the pullbacks of `N` along the members of a sieve which restricts to an fpqc covering of `O`,
compatible with further pullback, comes from a section of `N` over `O`. -/
theorem exists_sections_of_mem_fpqcTopology (N : X.Modules) [N.IsQuasicoherent] {O : X.Opens}
    (R : Sieve X) (hR : Sieve.pullback O.ι R ∈ Scheme.fpqcTopology O.toScheme)
    (x : ∀ ⦃Z : Scheme.{u}⦄ (y : Z ⟶ X), R y → Γ((pullback y).obj N, y ⁻¹ᵁ O))
    (hx : ∀ ⦃Z Z' : Scheme.{u}⦄ (y : Z ⟶ X) (hy : R y) (g : Z' ⟶ Z),
      x (g ≫ y) (R.downward_closed hy g) =
        ((pullbackComp g y).hom.app N).app _ (pullbackUnitApp g _ (y ⁻¹ᵁ O) (x y hy))) :
    ∃ s : Γ(N, O), ∀ ⦃Z : Scheme.{u}⦄ (y : Z ⟶ X) (hy : R y),
      pullbackUnitApp y N O s = x y hy := by
  have hsheaf := isSheafFor_presheafHom_of_mem_over (unit X) N
    (SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)) inferInstance _
    (GrothendieckTopology.overEquiv_symm_mem_over _ (Over.mk O.ι) _ hR)
  have hV {V : Over X} (g : V ⟶ Over.mk O.ι) : V.hom ⁻¹ᵁ O = ⊤ := by
    rw [← Over.w g, Scheme.Hom.comp_preimage]
    exact congrArg (g.left ⁻¹ᵁ ·) O.ι_preimage_self
  have hRV {V : Over X} (g : V ⟶ Over.mk O.ι)
      (hg : ((Sieve.overEquiv (Over.mk O.ι)).symm (Sieve.pullback O.ι R)).arrows g) :
      R V.hom := by
    rw [← Over.w g]
    exact hg
  let xf : Presieve.FamilyOfElements (modulesPseudofunctor.presheafHom (unit X) N)
      ((Sieve.overEquiv (Over.mk O.ι)).symm (Sieve.pullback O.ι R)).arrows :=
    fun V g hg ↦ Function.surjInv (bijective_homSectionAt V.hom (A := N) (hV g)).2
      (x V.hom (hRV g hg))
  have hxf {V : Over X} (g : V ⟶ Over.mk O.ι)
      (hg : ((Sieve.overEquiv (Over.mk O.ι)).symm (Sieve.pullback O.ι R)).arrows g) :
      homSectionAt V.hom O (xf g hg) = x V.hom (hRV g hg) :=
    Function.surjInv_eq _ _
  have hcompat : xf.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W g f hg
    apply (bijective_homSectionAt W.hom (A := N) (hV (f ≫ g))).1
    rw [hxf (f ≫ g) (Sieve.downward_closed _ hg f), Pseudofunctor.presheafHom_map_eq_pullHom,
      homSectionAt_pullHom_of_eq_family R x hx V.hom (hRV g hg) f.left W.hom (Over.w f) _ _
        (hxf g hg)]
  obtain ⟨φ, hφ, -⟩ := hsheaf xf hcompat
  obtain ⟨s, hs⟩ := (bijective_pullbackUnit_app_of_isOpenImmersion O.ι N O.opensRange_ι.ge).2
    (homSectionAt O.ι O φ)
  have h0 {V : Over X} (g : V ⟶ Over.mk O.ι)
      (hg : ((Sieve.overEquiv (Over.mk O.ι)).symm (Sieve.pullback O.ι R)).arrows g) :
      pullbackUnitApp V.hom N O s = x V.hom (hRV g hg) := by
    rw [← hxf g hg, ← hφ g hg, Pseudofunctor.presheafHom_map_eq_pullHom,
      homSectionAt_pullHom_of_eq O.ι g.left V.hom (Over.w g) s φ hs.symm]
  have h1 ⦃Z : Scheme.{u}⦄ (y : Z ⟶ X) (hy : R y) (hy' : y ⁻¹ᵁ O = ⊤) :
      pullbackUnitApp y N O s = x y hy := by
    have hrange : Set.range y.base ⊆ Set.range O.ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      have hz : z ∈ y ⁻¹ᵁ O := hy' ▸ trivial
      exact hz
    obtain ⟨y', hy'⟩ : ∃ y' : Z ⟶ O.toScheme, y' ≫ O.ι = y :=
      ⟨_, IsOpenImmersion.lift_fac O.ι y hrange⟩
    subst hy'
    exact h0 (V := Over.mk (y' ≫ O.ι)) (Over.homMk y') hy
  refine ⟨s, fun Z y hy ↦ ?_⟩
  apply (bijective_pullbackUnit_app_of_isOpenImmersion (y ⁻¹ᵁ O).ι ((pullback y).obj N)
    (y ⁻¹ᵁ O).opensRange_ι.ge).1
  have hjy : ((y ⁻¹ᵁ O).ι ≫ y) ⁻¹ᵁ O = ⊤ := by
    rw [Scheme.Hom.comp_preimage]
    exact (y ⁻¹ᵁ O).ι_preimage_self
  refine ((pullbackUnit_comp_app_apply (y ⁻¹ᵁ O).ι y N O s).symm.trans
    (congrArg _ (h1 ((y ⁻¹ᵁ O).ι ≫ y) (R.downward_closed hy _) hjy))).trans ?_
  rw [hx y hy]
  exact congr(Hom.app $((pullbackComp (y ⁻¹ᵁ O).ι y).hom_inv_id_app N) _ _)

end Scheme.Modules

end AlgebraicGeometry
