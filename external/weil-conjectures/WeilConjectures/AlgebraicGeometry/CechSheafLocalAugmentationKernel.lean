/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
/-! # The degree-zero kernel of a locally restricted Cech augmentation

Source: blueprint `lemma-coherent-base-change-invertible-sheaves`, proof paragraph 1.
(blueprint: lem-pc-cech-local-augmentation-kernel).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem augmentation_injective_on_open
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (F G : X.Modules)
    (a : F ⟶ G)
    (e : G.presheafModuleCat ≅
      ((cechComplexFunctor U).obj
        ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
          (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).X 0)
    (hε : ∀ (y : Fin 1 → ι) (V : X.Opens),
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            a.val ≫
          e.hom ≫
            Pi.π (fun y : Fin 1 → ι =>
              ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
                (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat).obj
                  (op (∏ᶜ fun l => U (y l)))) y).app (op V) =
          F.presheafModuleCat.map (prod.snd : (∏ᶜ fun l => U (y l)) ⨯ V ⟶ V).op)
    (i : ι) (V : X.Opens) (hV : V ≤ U i) :
    Function.Injective (a.val.app (op V)) := by
  intro x y hxy
  let q : V ⟶ ∏ᶜ (fun _ : Fin 1 ↦ U i) := Pi.lift (fun _ ↦ homOfLE hV)
  let r : V ⟶ (∏ᶜ (fun _ : Fin 1 ↦ U i)) ⨯ V := prod.lift q (𝟙 V)
  have hr : r ≫ prod.snd = 𝟙 V := by simp [r]
  have h := ConcreteCategory.congr_hom (hε (fun _ ↦ i) V) x
  have h' := ConcreteCategory.congr_hom (hε (fun _ ↦ i) V) y
  have hx : F.presheafModuleCat.map
      (prod.snd : (∏ᶜ (fun _ : Fin 1 ↦ U i)) ⨯ V ⟶ V).op x =
      F.presheafModuleCat.map
      (prod.snd : (∏ᶜ (fun _ : Fin 1 ↦ U i)) ⨯ V ⟶ V).op y := by
    erw [← h, ← h']
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
    congr 1
    congr 1
  have hh := congrArg (F.presheafModuleCat.map r.op) hx
  simpa only [← ConcreteCategory.comp_apply, ← F.presheafModuleCat.map_comp,
    ← op_comp, hr, op_id, F.presheafModuleCat.map_id, ConcreteCategory.id_apply] using hh

/-- A zero cocycle on an open inside a member of the family is a restriction family.
Source: blueprint `lemma-coherent-base-change-invertible-sheaves`, proof paragraph 1.
(blueprint: lem-pc-cech-local-augmentation-kernel)

Proof: Put P(W)(V)=F(W x V), with the global structure-ring action. For the singleton
constant tuple i, form r_i:V -> (product of the singleton U_i) x V using V <= U_i
and the identity of V. Project z to this singleton and restrict along r_i; call the
result x. For each singleton tuple y, put j=y(0) and project the equation d z=0
onto the pair (i,j). The alternating sum has exactly two terms: the restriction
of z_j minus the restriction of z_i. Pull this equality back along
(product of the singleton U_j) x V -> (product of the pair (U_i,U_j)) x V,
whose U_i component uses V <= U_i, whose U_j component is the singleton projection,
and whose V component is the projection to V. The j composite is the identity
on (product of the singleton U_j) x V; the i composite factors through r_i
and the projection to V. Functoriality gives z_j=restriction(x). Since every
Fin 1 tuple is constant, this is the required equation for every y. This uses
only finite-product identities and the two-coface degree-zero differential;
no cover condition, sheaf gluing, local-ring linearity, or positive-degree
exactness is used. For the empty open the same morphism identities apply, and
an empty index type supplies no i. -/
private theorem cech_local_zero_cocycle_reconstruction
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (F : X.Modules)
    (i : ι) (V : X.Opens) (hV : V ≤ U i)
    (z : (((cechComplexFunctor U).obj
      ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).X 0).obj (op V))
    (hz : (((cechComplexFunctor U).obj
      ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).d 0 1).app (op V) z = 0) :
    ∃ x : F.presheafModuleCat.obj (op V), ∀ y : Fin 1 → ι,
      (Pi.π (fun y : Fin 1 → ι ↦
        ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
          (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat).obj
            (op (∏ᶜ fun l ↦ U (y l)))) y).app (op V) z =
      F.presheafModuleCat.map (prod.snd : (∏ᶜ fun l ↦ U (y l)) ⨯ V ⟶ V).op x := by
  let P := (prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat
  let T := (FormalCoproduct.mk _ U).cech
  let Q := (FormalCoproduct.cosimplicialObjectFunctor T).obj P
  let ci := (Pi.π (fun s : Fin 1 → ι ↦ P.obj (op (∏ᶜ fun k ↦ U (s k)))))
    (fun _ ↦ i)
  let qi : V ⟶ ∏ᶜ (fun _ : Fin 1 ↦ U i) := Pi.lift (fun _ ↦ homOfLE hV)
  let ri : V ⟶ (∏ᶜ (fun _ : Fin 1 ↦ U i)) ⨯ V := prod.lift qi (𝟙 V)
  refine ⟨F.presheafModuleCat.map ri.op (ci.app (op V) z), ?_⟩
  intro y
  have hy : y = fun _ ↦ y 0 := by
    funext k
    congr 1
    exact Subsingleton.elim _ _
  rw [hy]
  generalize y 0 = j
  change (∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) • Q.δ k).app (op V) z = 0 at hz
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_zsmul, neg_one_zsmul, ← sub_eq_add_neg] at hz
  have hz' : (Q.δ 0).app (op V) z = (Q.δ 1).app (op V) z := by
    simpa only [NatTrans.app_sub, ModuleCat.hom_sub, LinearMap.sub_apply, sub_eq_zero] using hz
  let t : Fin 2 → ι := Fin.cases i (fun _ ↦ j)
  have h := congrArg (fun w ↦ (Pi.π (fun s : Fin 2 → ι ↦
    P.obj (op (∏ᶜ fun k ↦ U (s k)))) t).app (op V) w) hz'
  change ((Q.δ 0 ≫ Pi.π _ t).app (op V)) z =
    ((Q.δ 1 ≫ Pi.π _ t).app (op V)) z at h
  have hδ (k : Fin 2) : Q.δ k ≫ Pi.π _ t =
      Pi.π (fun s : Fin 1 → ι ↦ P.obj (op (∏ᶜ fun a ↦ U (s a))))
        (t ∘ ⇑(Fin.succAboveOrderEmb k).toOrderHom) ≫
      P.map (Pi.lift (fun a : Fin 1 ↦ Pi.π (fun a : Fin 2 ↦ U (t a))
        ((Fin.succAboveOrderEmb k).toOrderHom a))).op := by
    dsimp [Q, T, FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp,
      CosimplicialObject.δ, FormalCoproduct.cech, FormalCoproduct.mapPower,
      FormalCoproduct.power, SimplexCategory.δ]
    erw [Pi.lift_comp_π]
    rfl
  rw [hδ, hδ] at h
  have h0 : (⇑(Fin.succAboveOrderEmb (0 : Fin 2)).toOrderHom) =
      (fun _ : Fin 1 ↦ (1 : Fin 2)) := by
    funext k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    rfl
  have h1 : (⇑(Fin.succAboveOrderEmb (1 : Fin 2)).toOrderHom) =
      (fun _ : Fin 1 ↦ (0 : Fin 2)) := by
    funext k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    rfl
  rw [h0, h1] at h
  dsimp [Function.comp_def, t] at h
  let cj := Pi.π (fun s : Fin 1 → ι ↦ P.obj (op (∏ᶜ fun k ↦ U (s k))))
    (fun _ ↦ j)
  let di : (∏ᶜ (fun k : Fin 2 ↦ U (t k))) ⟶ ∏ᶜ (fun _ : Fin 1 ↦ U i) :=
    Pi.lift (fun _ ↦ Pi.π _ 0)
  let dj : (∏ᶜ (fun k : Fin 2 ↦ U (t k))) ⟶ ∏ᶜ (fun _ : Fin 1 ↦ U j) :=
    Pi.lift (fun _ ↦ Pi.π _ 1)
  change ((cj ≫ P.map dj.op).app (op V)) z =
    ((ci ≫ P.map di.op).app (op V)) z at h
  let Wj := (∏ᶜ (fun _ : Fin 1 ↦ U j)) ⨯ V
  let a : Wj ⟶ U i := prod.snd ≫ homOfLE hV
  let b : Wj ⟶ U j := prod.fst ≫ Pi.π _ 0
  let l : Wj ⟶ (∏ᶜ (fun k : Fin 2 ↦ U (t k))) ⨯ V :=
    prod.lift (Pi.lift (Fin.cases a (fun _ ↦ b))) prod.snd
  let fi := prod.map di (𝟙 V)
  let fj := prod.map dj (𝟙 V)
  have hi : l ≫ fi = prod.snd ≫ ri := Subsingleton.elim _ _
  have hj : l ≫ fj = 𝟙 Wj := Subsingleton.elim _ _
  change F.presheafModuleCat.map fj.op (cj.app (op V) z) =
    F.presheafModuleCat.map fi.op (ci.app (op V) z) at h
  have hh := congrArg (F.presheafModuleCat.map l.op) h
  simp only [← ConcreteCategory.comp_apply, ← F.presheafModuleCat.map_comp,
    ← op_comp, hj, hi, op_id] at hh
  rw [F.presheafModuleCat.map_id, ConcreteCategory.id_apply] at hh
  simpa only [op_comp, F.presheafModuleCat.map_comp, ConcreteCategory.comp_apply,
    ci, cj] using hh


private theorem restricted_kernel_of_sectionwise
    {X : Scheme.{u}} (W : X.Opens) (F G H : X.Modules)
    (a : F ⟶ G) (b : G ⟶ H) (hab : a ≫ b = 0)
    (hinj : ∀ (V : X.Opens), V ≤ W → Function.Injective (a.val.app (op V)))
    (hsurj : ∀ (V : X.Opens), V ≤ W → ∀ z : G.val.obj (op V),
      b.val.app (op V) z = 0 → ∃ x : F.val.obj (op V), a.val.app (op V) x = z) :
    Nonempty (IsLimit (KernelFork.ofι ((Scheme.Modules.restrictFunctor W.ι).map a)
      (show (Scheme.Modules.restrictFunctor W.ι).map a ≫
          (Scheme.Modules.restrictFunctor W.ι).map b = 0 by
        rw [← Functor.map_comp, hab, Functor.map_zero]))) := by
  let R := Scheme.Modules.restrictFunctor W.ι
  let aa := R.map a
  let bb := R.map b
  have hzero : aa ≫ bb = 0 := by
    dsimp [aa, bb]
    rw [← R.map_comp, hab, R.map_zero]
  let l := kernel.lift bb aa hzero
  have hl : l ≫ kernel.ι bb = aa := kernel.lift_ι _ _ _
  have ha : ∀ V, Function.Injective (aa.val.app V) := by
    intro V
    exact hinj (W.ι ''ᵁ V.unop)
      (by simpa only [Scheme.Opens.opensRange_ι] using W.ι.image_le_opensRange V.unop)
  have hs : ∀ V, ∀ z : (R.obj G).val.obj V,
      bb.val.app V z = 0 → ∃ x : (R.obj F).val.obj V, aa.val.app V x = z := by
    intro V z hz
    exact hsurj (W.ι ''ᵁ V.unop)
      (by simpa only [Scheme.Opens.opensRange_ι] using W.ι.image_le_opensRange V.unop) z hz
  have : Mono l.val := PresheafOfModules.mono_of_injective (by
    intro V x y hxy
    apply ha V
    have hh := congrArg ((kernel.ι bb).val.app V) hxy
    simpa only [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app,
      ← SheafOfModules.comp_val, hl] using hh)
  have : Epi l.val := PresheafOfModules.epi_of_surjective (by
    intro V z
    let k := (kernel.ι bb).val.app V
    have hz : bb.val.app V (k z) = 0 := by
      have hh := ConcreteCategory.congr_hom
        (congrArg (fun f ↦ f.val.app V) (kernel.condition bb)) z
      change bb.val.app V (k z) = 0 at hh
      exact hh
    obtain ⟨x, hx⟩ := hs V (k z) hz
    refine ⟨x, ?_⟩
    apply Scheme.Modules.injective_map_kernelι V.unop bb
    have hh := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.val.app V) hl) x
    change (kernel.ι bb).val.app V (l.val.app V x) = aa.val.app V x at hh
    exact hh.trans hx)
  have : IsIso l.val := isIso_of_mono_of_epi l.val
  let el : R.obj F ≅ kernel bb :=
    { hom := l
      inv := ⟨inv l.val⟩
      hom_inv_id := by
        apply SheafOfModules.hom_ext
        exact IsIso.hom_inv_id l.val
      inv_hom_id := by
        apply SheafOfModules.hom_ext
        exact IsIso.inv_hom_id l.val }
  exact ⟨IsLimit.ofIsoLimit (kernelIsKernel bb)
    (Fork.ext el.symm (by
      change el.inv ≫ aa = kernel.ι bb
      rw [← hl, ← Category.assoc]
      change el.inv ≫ el.hom ≫ kernel.ι bb = kernel.ι bb
      exact el.inv_hom_id_assoc _))⟩

/-- The restricted augmentation is the kernel of the first differential.
Source: blueprint `lemma-coherent-base-change-invertible-sheaves`, proof paragraph 1.
(blueprint: lem-pc-cech-local-augmentation-kernel)

Proof: On an open V contained in U_i, identify the singleton i coordinate with F(V).
Project a zero cocycle to that coordinate. The pair (i,j) coordinate of d^0 says that
its j coordinate is the restriction of this section. Thus every zero cocycle is
uniquely the restriction augmentation of a section of F(V). The specified augmentation
formula identifies this map with the given augmentation, and hd in degree zero identifies
zero cocycles through e. All these bijections commute with restriction. Their inverses
are linear over the local structure ring: the augmentation is a module-sheaf morphism,
and an inverse to a bijective linear map is linear. Consequently they define a kernel
universal property in module sheaves on U_i. The single-complex degree-zero object is
canonically F restricted to U_i. On the empty open all sections are zero, so the same
argument applies. Neither a covering hypothesis nor any positive-degree exactness is
used. -/
theorem augmented_cech_sheaf_restrict_kernel
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (F : X.Modules)
    (D : CochainComplex X.Modules ℕ)
    (ε : (CochainComplex.single₀ X.Modules).obj F ⟶ D)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor U).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor U).obj
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).d p (p + 1))
    (hε : ∀ (y : Fin 1 → ι) (V : X.Opens),
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv ≫ ε.f 0).val ≫
          (e 0).hom ≫
            Pi.π (fun y : Fin 1 → ι =>
              ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
                (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat).obj
                  (op (∏ᶜ fun l => U (y l)))) y).app (op V) =
          F.presheafModuleCat.map (prod.snd : (∏ᶜ fun l => U (y l)) ⨯ V ⟶ V).op) (i : ι) :
    Nonempty (IsLimit (KernelFork.ofι
      ((((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).map ε).f 0)
      (show (((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).map ε).f 0 ≫
          (((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D).d 0 1 = 0 by
        rw [HomologicalComplex.Hom.comm]
        simp))) := by
  let a := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv ≫ ε.f 0
  have hab : a ≫ D.d 0 1 = 0 := by
    dsimp [a]
    rw [Category.assoc, ε.comm]
    simp
  have hinj := augmentation_injective_on_open U F (D.X 0) a (e 0) hε i
  have hsurj : ∀ (V : X.Opens), V ≤ U i → ∀ z : (D.X 0).val.obj (op V),
      (D.d 0 1).val.app (op V) z = 0 →
        ∃ x : F.val.obj (op V), a.val.app (op V) x = z := by
    intro V hV z hz
    let L := (cechComplexFunctor U).obj
      ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)
    let zz := (e 0).hom.app (op V) z
    have hzz : (L.d 0 1).app (op V) zz = 0 := by
      have hh := ConcreteCategory.congr_hom (NatTrans.congr_app (hd 0) (op V)) z
      change (e 1).hom.app (op V) ((D.d 0 1).val.app (op V) z) =
        (L.d 0 1).app (op V) zz at hh
      rw [hz, map_zero] at hh
      exact hh.symm
    obtain ⟨x, hx⟩ := cech_local_zero_cocycle_reconstruction U F i V hV zz hzz
    refine ⟨x, ?_⟩
    apply (ModuleCat.mono_iff_injective ((e 0).hom.app (op V))).1 inferInstance
    change (e 0).hom.app (op V) (a.val.app (op V) x) = zz
    let P := fun y : Fin 1 → ι ↦
      ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat).obj
          (op (∏ᶜ fun l ↦ U (y l)))
    let ev := (CategoryTheory.evaluation X.Opensᵒᵖ (ModuleCat Γ(X, ⊤))).obj (op V)
    apply Concrete.isLimit_ext _
      (isLimitOfHasProductOfPreservesLimit ev P) _ _
    intro y
    change (Pi.π P y.as).app (op V)
      ((e 0).hom.app (op V) (a.val.app (op V) x)) =
        (Pi.π P y.as).app (op V) zz
    have hh := ConcreteCategory.congr_hom (hε y.as V) x
    change (Pi.π P y.as).app (op V)
      ((e 0).hom.app (op V) (a.val.app (op V) x)) = _ at hh
    exact hh.trans (hx y.as).symm
  obtain ⟨hk⟩ := restricted_kernel_of_sectionwise (U i) F (D.X 0) (D.X 1)
    a (D.d 0 1) hab hinj hsurj
  let R := Scheme.Modules.restrictFunctor (U i).ι
  let s := HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F
  exact ⟨IsLimit.ofIsoLimit hk
    (Fork.ext (R.mapIso s).symm (by
      change R.map s.inv ≫ R.map (ε.f 0) = R.map a
      rw [← R.map_comp]))⟩

end AlgebraicGeometry
