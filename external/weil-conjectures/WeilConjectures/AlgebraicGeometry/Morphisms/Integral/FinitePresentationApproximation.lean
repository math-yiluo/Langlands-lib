/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.Limit
public import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FiniteApproximation

/-!
# Integral morphisms are limits of finite morphisms of finite presentation

We show that an integral morphism `f : X ⟶ S` to a quasi-compact quasi-separated scheme presents
`X` as a cofiltered limit of schemes which are finite and of finite presentation over `S`
(`AlgebraicGeometry.Scheme.Hom.exists_finiteApproximation_of_isIntegralHom`, Stacks Project
Tag 09YZ).

Start from a presentation `X = lim Tᵢ` with `Tᵢ` finite over `S`
(`AlgebraicGeometry.Scheme.Hom.nonempty_finiteApproximation_of_isIntegralHom`). Every finite
`S`-scheme `Tᵢ` is a closed subscheme of a finite `S`-scheme `Yᵢ` of finite presentation
(`AlgebraicGeometry.Scheme.Hom.nonempty_closedFPEmbedding`), and `Tᵢ` is the limit of the closed
subschemes `V(K) ⊆ Yᵢ` cut out by the subideal sheaves `K` of finite type of the ideal sheaf of
`Tᵢ` (Stacks Project Tag 09ZP); these are finite and of finite presentation over `S`. The index
category has objects the pairs `(i, K)` and morphisms the `S`-morphisms `V(K) ⟶ V(K')` under `X`.
It is cofiltered because morphisms from a limit to a scheme of finite presentation factor through
a stage, uniquely up to passing to a further stage (Stacks Project Tag 01ZC).

## References

* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
* [Stacks Project, Tag 09ZP](https://stacks.math.columbia.edu/tag/09ZP)
* [Stacks Project, Tag 09ZQ](https://stacks.math.columbia.edu/tag/09ZQ)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)

## Implementation details

The declarations in the namespace `AlgebraicGeometry.Scheme.Hom.FiniteApproximation` (`FPIndex`,
`fpObj`, `fpDiagram`, `isLimitFpCone`, ...) are auxiliary to this construction.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A closed immersion of an `S`-scheme into a finite `S`-scheme of finite presentation. -/
structure Scheme.Hom.ClosedFPEmbedding {T S : Scheme.{u}} (p : T ⟶ S) where
  /-- The ambient scheme. -/
  Y : Scheme.{u}
  /-- The closed immersion. -/
  e : T ⟶ Y
  /-- The structure morphism of the ambient scheme. -/
  q : Y ⟶ S
  [isClosedImmersion_e : IsClosedImmersion e]
  [isFinite_q : IsFinite q]
  [locallyOfFinitePresentation_q : LocallyOfFinitePresentation q]
  e_q : e ≫ q = p

attribute [instance] Scheme.Hom.ClosedFPEmbedding.isClosedImmersion_e
  Scheme.Hom.ClosedFPEmbedding.isFinite_q
  Scheme.Hom.ClosedFPEmbedding.locallyOfFinitePresentation_q

instance Scheme.Hom.ClosedFPEmbedding.compactSpace_Y {T S : Scheme.{u}} {p : T ⟶ S}
    (P : p.ClosedFPEmbedding) [CompactSpace S] : CompactSpace P.Y :=
  QuasiCompact.compactSpace_of_compactSpace P.q

instance Scheme.Hom.ClosedFPEmbedding.quasiSeparatedSpace_Y {T S : Scheme.{u}} {p : T ⟶ S}
    (P : p.ClosedFPEmbedding) [QuasiSeparatedSpace S] : QuasiSeparatedSpace P.Y :=
  quasiSeparatedSpace_of_quasiSeparated P.q

/-- **A finite scheme over a quasi-compact quasi-separated base is a closed subscheme of a finite
scheme of finite presentation.** -/
theorem Scheme.Hom.nonempty_closedFPEmbedding {T S : Scheme.{u}} (p : T ⟶ S) [IsFinite p]
    [CompactSpace S] [QuasiSeparatedSpace S] : Nonempty p.ClosedFPEmbedding := by
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace T := quasiSeparatedSpace_of_quasiSeparated p
  obtain ⟨A⟩ := p.nonempty_finitePresentationApproximation
  obtain ⟨K, hK⟩ := Scheme.exists_isFinite_of_isLimit A.D _ A.isLimit (fun K ↦ A.p.app K)
    (fun g ↦ (A.p.naturality g).trans (Category.comp_id _)) p A.w
  exact ⟨{ Y := A.D.obj K, e := A.π.app K, q := A.p.app K, e_q := A.w K }⟩

namespace Scheme.Hom.FiniteApproximation

open Scheme.IdealSheafData

variable {X S : Scheme.{u}} {f : X ⟶ S} (F : f.FiniteApproximation)
  (E : ∀ i, (F.p i).ClosedFPEmbedding)

/-- The index type of the finitely presented approximation: pairs of an index `i` of `F` and a
subideal sheaf of finite type of the ideal sheaf of `F.D.obj i` in its finitely presented
ambient. -/
abbrev FPIndex : Type u := Σ i : F.I, ((E i).e.ker.FGSub)

variable {F E}

/-- The stage `V(K)` attached to an index. -/
noncomputable abbrev fpObj (c : FPIndex F E) : Scheme.{u} := c.2.1.subscheme

/-- The structure morphism of a stage. -/
noncomputable abbrev fpP (c : FPIndex F E) : fpObj c ⟶ S := c.2.1.subschemeι ≫ (E c.1).q

lemma ker_le_ker (c : FPIndex F E) : c.2.1.subschemeι.ker ≤ (E c.1).e.ker := by
  rw [ker_subschemeι]; exact c.2.2.1

/-- The closed immersion of `F.D.obj i` into a stage. -/
noncomputable abbrev fpT (c : FPIndex F E) : F.D.obj c.1 ⟶ fpObj c :=
  IsClosedImmersion.lift c.2.1.subschemeι (E c.1).e (ker_le_ker c)

@[reassoc (attr := simp)]
lemma fpT_ι (c : FPIndex F E) : fpT c ≫ c.2.1.subschemeι = (E c.1).e :=
  IsClosedImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
lemma fpT_fpP (c : FPIndex F E) : fpT c ≫ fpP c = F.p c.1 := by
  simp [fpP, (E c.1).e_q]

/-- The morphism from `X` to a stage. -/
noncomputable abbrev fpH (c : FPIndex F E) : X ⟶ fpObj c := F.π.app c.1 ≫ fpT c

lemma π_app_map {i j : F.I} (g : i ⟶ j) : F.π.app i ≫ F.D.map g = F.π.app j := by
  simpa using (F.π.naturality g).symm

/-- The morphisms of the index category: `S`-morphisms under `X`. -/
def FPHom (c d : FPIndex F E) : Type u :=
  {g : fpObj c ⟶ fpObj d // fpH c ≫ g = fpH d ∧ g ≫ fpP d = fpP c}

noncomputable instance : SmallCategory (FPIndex F E) where
  Hom := FPHom
  id c := ⟨𝟙 _, Category.comp_id _, Category.id_comp _⟩
  comp g g' := ⟨g.1 ≫ g'.1, by rw [← Category.assoc, g.2.1, g'.2.1],
    by rw [Category.assoc, g'.2.2, g.2.2]⟩
  id_comp g := Subtype.ext (Category.id_comp _)
  comp_id g := Subtype.ext (Category.comp_id _)
  assoc g g' g'' := Subtype.ext (Category.assoc _ _ _)

lemma fpHom_comp_val {c d e : FPIndex F E} (g : c ⟶ d) (g' : d ⟶ e) :
    (g ≫ g').1 = g.1 ≫ g'.1 := rfl

lemma fpHom_id_val (c : FPIndex F E) : (𝟙 c : c ⟶ c).1 = 𝟙 _ := rfl


/-- The morphism `V(K') ⟶ V(K)` for `K ≤ K'`. -/
noncomputable def fpIncl (i : F.I) {K K' : (E i).e.ker.FGSub} (h : K ≤ K') :
    (⟨i, K'⟩ : FPIndex F E) ⟶ ⟨i, K⟩ :=
  ⟨inclusion h, by
    simp only [fpH, Category.assoc]
    congr 1
    rw [← cancel_mono (K.1.subschemeι), Category.assoc, inclusion_subschemeι, fpT_ι, fpT_ι],
    by simp [fpP]⟩


section Stage

variable (F E) [CompactSpace S] [QuasiSeparatedSpace S] (i : F.I)

/-- The structure morphisms of the closed subschemes of the ambient of
`F.D.obj i` cut out by the subideal sheaves of finite type. -/
@[simps]
noncomputable def fgSubP : (E i).e.ker.fgSubDiagram ⟶ (Functor.const _).obj S where
  app K := K.unop.1.subschemeι ≫ (E i).q
  naturality K K' g := by simp

/-- `F.D.obj i` is the closed subscheme cut out by its ideal sheaf. -/
noncomputable abbrev fpφ : F.D.obj i ⟶ (E i).e.ker.subscheme :=
  IsClosedImmersion.lift (E i).e.ker.subschemeι (E i).e (by rw [ker_subschemeι])

instance : IsIso (fpφ F E i) :=
  IsClosedImmersion.isIso_of_ker_eq (E i).e (E i).e.ker.subschemeι _
    (IsClosedImmersion.lift_fac _ _ _) (ker_subschemeι _).symm

omit [CompactSpace S] [QuasiSeparatedSpace S] in
variable {F E} in
lemma fpT_eq (K : (E i).e.ker.FGSub) :
    fpT (⟨i, K⟩ : FPIndex F E) = fpφ F E i ≫ (E i).e.ker.fgSubCone.π.app (.op K) := by
  rw [← cancel_mono K.1.subschemeι, fpT_ι, Category.assoc, fgSubCone_π_app,
    inclusion_subschemeι, IsClosedImmersion.lift_fac]

variable {F E}

lemma exists_fpT_comp_eq {d : FPIndex F E} (a : F.D.obj i ⟶ fpObj d)
    (ha : a ≫ fpP d = F.p i) :
    ∃ (K : (E i).e.ker.FGSub) (g : fpObj (⟨i, K⟩ : FPIndex F E) ⟶ fpObj d),
      fpT ⟨i, K⟩ ≫ g = a ∧ g ≫ fpP d = fpP ⟨i, K⟩ := by
  have : CompactSpace (E i).Y := QuasiCompact.compactSpace_of_compactSpace (E i).q
  have : QuasiSeparatedSpace (E i).Y := quasiSeparatedSpace_of_quasiSeparated (E i).q
  obtain ⟨K, g, hg₁, hg₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (E i).e.ker.fgSubDiagram (fgSubP F E i) (fpP d) (E i).e.ker.fgSubCone
    (E i).e.ker.isLimitFgSubCone (inv (fpφ F E i) ≫ a) (by
      ext K
      simp only [NatTrans.comp_app, Functor.const_obj_obj, fgSubCone_π_app, fgSubP_app,
        inclusion_subschemeι_assoc, Functor.const_map_app, Category.assoc, ha]
      rw [IsIso.eq_inv_comp, IsClosedImmersion.lift_fac_assoc, (E i).e_q])
  refine ⟨K.unop, g, ?_, hg₂⟩
  rw [fpT_eq, Category.assoc, hg₁, IsIso.hom_inv_id_assoc]

lemma exists_inclusion_comp_eq (K : (E i).e.ker.FGSub) {d : FPIndex F E}
    (g g' : fpObj (⟨i, K⟩ : FPIndex F E) ⟶ fpObj d) (hg : g ≫ fpP d = fpP ⟨i, K⟩)
    (hg' : g' ≫ fpP d = fpP ⟨i, K⟩) (h : fpT ⟨i, K⟩ ≫ g = fpT ⟨i, K⟩ ≫ g') :
    ∃ (K' : (E i).e.ker.FGSub) (hK : K ≤ K'), inclusion hK ≫ g = inclusion hK ≫ g' := by
  have : CompactSpace (E i).Y := QuasiCompact.compactSpace_of_compactSpace (E i).q
  have : QuasiSeparatedSpace (E i).Y := quasiSeparatedSpace_of_quasiSeparated (E i).q
  rw [fpT_eq, Category.assoc, Category.assoc, cancel_epi] at h
  obtain ⟨k, hik, hjk, hk⟩ := Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType
    (E i).e.ker.fgSubDiagram (fgSubP F E i) (fpP d) (E i).e.ker.fgSubCone
    (E i).e.ker.isLimitFgSubCone (i := .op K) g hg.symm (j := .op K) g' hg'.symm h
  have : hik = hjk := Subsingleton.elim _ _
  subst this
  exact ⟨k.unop, leOfHom hik.unop, hk⟩


end Stage

variable (F) in
/-- The structure morphisms of `F` as a natural transformation. -/
@[simps]
def pNatTrans : F.D ⟶ (Functor.const F.I).obj S where
  app := F.p
  naturality i j g := by simp [F.map_p]

/-- The morphism of the index category given by a factorization. -/
def fpHomMk {j : F.I} {K : (E j).e.ker.FGSub} {c : FPIndex F E} (g : fpObj ⟨j, K⟩ ⟶ fpObj c)
    {i : F.I} (w : j ⟶ i) (hc : c.1 = i) (hg : fpT ⟨j, K⟩ ≫ g = F.D.map w ≫ (hc ▸ fpT c))
    (hq : g ≫ fpP c = fpP ⟨j, K⟩) : (⟨j, K⟩ : FPIndex F E) ⟶ c := by
  subst hc
  refine ⟨g, ?_, hq⟩
  rw [Category.assoc, hg, ← Category.assoc, π_app_map]

variable [CompactSpace S] [QuasiSeparatedSpace S]

instance : IsCofiltered (FPIndex F E) where
  nonempty := by
    obtain ⟨i⟩ := IsCofiltered.nonempty (C := F.I)
    exact ⟨⟨i, ⊥⟩⟩
  cone_objs c₁ c₂ := by
    obtain ⟨j, f₁, f₂, -⟩ := IsCofilteredOrEmpty.cone_objs c₁.1 c₂.1
    obtain ⟨K₁, g₁, hg₁, hg₁'⟩ := exists_fpT_comp_eq j (F.D.map f₁ ≫ fpT c₁)
      (by rw [Category.assoc, fpT_fpP, F.map_p])
    obtain ⟨K₂, g₂, hg₂, hg₂'⟩ := exists_fpT_comp_eq j (F.D.map f₂ ≫ fpT c₂)
      (by rw [Category.assoc, fpT_fpP, F.map_p])
    obtain ⟨K, hK₁, hK₂⟩ := exists_ge_ge K₁ K₂
    exact ⟨⟨j, K⟩, fpIncl j hK₁ ≫ fpHomMk g₁ f₁ rfl hg₁ hg₁',
      fpIncl j hK₂ ≫ fpHomMk g₂ f₂ rfl hg₂ hg₂', trivial⟩
  cone_maps {c' c} u v := by
    have h : fpH c' ≫ u.1 = fpH c' ≫ v.1 := u.2.1.trans v.2.1.symm
    obtain ⟨k, hik, hjk, hk⟩ := Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType
      F.D (pNatTrans F) (fpP c) (Cone.mk X F.π) F.isLimit (i := c'.1) (fpT c' ≫ u.1)
      (by rw [Category.assoc, u.2.2, fpT_fpP]; rfl) (j := c'.1) (fpT c' ≫ v.1)
      (by rw [Category.assoc, v.2.2, fpT_fpP]; rfl) (by simpa using h)
    obtain ⟨k', e, he⟩ := IsCofilteredOrEmpty.cone_maps hik hjk
    have hw : F.D.map (e ≫ hik) ≫ fpT c' ≫ u.1 = F.D.map (e ≫ hik) ≫ fpT c' ≫ v.1 := by
      calc F.D.map (e ≫ hik) ≫ fpT c' ≫ u.1 = F.D.map e ≫ F.D.map hik ≫ fpT c' ≫ u.1 := by
            rw [Functor.map_comp, Category.assoc]
        _ = F.D.map e ≫ F.D.map hjk ≫ fpT c' ≫ v.1 := by rw [hk]
        _ = F.D.map (e ≫ hjk) ≫ fpT c' ≫ v.1 := by rw [Functor.map_comp, Category.assoc]
        _ = _ := by rw [he]
    obtain ⟨K₁, g₁, hg₁, hg₁'⟩ := exists_fpT_comp_eq k' (F.D.map (e ≫ hik) ≫ fpT c')
      (by rw [Category.assoc, fpT_fpP, F.map_p])
    let m := fpHomMk g₁ (e ≫ hik) rfl hg₁ hg₁'
    obtain ⟨K₂, hK, hincl⟩ := exists_inclusion_comp_eq k' K₁ (g₁ ≫ u.1) (g₁ ≫ v.1)
      (by rw [Category.assoc, u.2.2, hg₁']) (by rw [Category.assoc, v.2.2, hg₁'])
      (by rw [← Category.assoc, hg₁, Category.assoc, hw, ← Category.assoc, ← hg₁,
        Category.assoc])
    refine ⟨⟨k', K₂⟩, fpIncl k' hK ≫ m, Subtype.ext ?_⟩
    change inclusion hK ≫ g₁ ≫ u.1 = inclusion hK ≫ g₁ ≫ v.1
    simpa only [Category.assoc] using hincl


variable (F E)

/-- The diagram of the finite, finitely presented stages. -/
@[simps]
noncomputable def fpDiagram : FPIndex F E ⥤ Scheme.{u} where
  obj := fpObj
  map g := g.1

/-- The cone with point `X` over the finitely presented stages. -/
@[simps]
noncomputable def fpπ : (Functor.const (FPIndex F E)).obj X ⟶ fpDiagram F E where
  app := fpH
  naturality c d g := by simpa using g.2.1.symm

variable {F E}

/-- The cone over the closed subschemes of the ambient of `F.D.obj j` induced by
a cone over the finitely presented stages. -/
@[simps]
noncomputable def fgSubConeOfCone (s : Cone (fpDiagram F E)) (j : F.I) :
    Cone (E j).e.ker.fgSubDiagram where
  pt := s.pt
  π :=
  { app K := s.π.app ⟨j, K.unop⟩
    naturality K K' g := by
      exact (Category.id_comp _).trans (s.w (fpIncl j (leOfHom g.unop))).symm }

/-- The morphism to `F.D.obj j` induced by a cone over the finitely presented
stages. -/
noncomputable def fpLiftApp (s : Cone (fpDiagram F E)) (j : F.I) : s.pt ⟶ F.D.obj j :=
  (E j).e.ker.isLimitFgSubCone.lift (fgSubConeOfCone s j) ≫ inv (fpφ F E j)

lemma fpLiftApp_fpT (s : Cone (fpDiagram F E)) (j : F.I) (K : (E j).e.ker.FGSub) :
    fpLiftApp s j ≫ fpT ⟨j, K⟩ = s.π.app ⟨j, K⟩ := by
  rw [fpT_eq, fpLiftApp, Category.assoc, IsIso.inv_hom_id_assoc, IsLimit.fac]
  rfl

lemma fpLiftApp_e (s : Cone (fpDiagram F E)) (j : F.I) :
    fpLiftApp s j ≫ (E j).e = s.π.app ⟨j, ⊥⟩ ≫ (⊥ : (E j).e.ker.FGSub).1.subschemeι := by
  rw [← fpLiftApp_fpT s j ⊥, Category.assoc, fpT_ι]

lemma fpLiftApp_map (s : Cone (fpDiagram F E)) {j j' : F.I} (g : j ⟶ j') :
    fpLiftApp s j ≫ F.D.map g = fpLiftApp s j' := by
  rw [← cancel_mono (E j').e, fpLiftApp_e]
  obtain ⟨K, g₁, hg₁, hg₁'⟩ := exists_fpT_comp_eq j
    (F.D.map g ≫ fpT (⟨j', ⊥⟩ : FPIndex F E)) (by rw [Category.assoc, fpT_fpP, F.map_p])
  let m := fpHomMk g₁ g rfl hg₁ hg₁'
  have h₁ : F.D.map g ≫ (E j').e =
      fpT (⟨j, K⟩ : FPIndex F E) ≫ g₁ ≫ (⊥ : (E j').e.ker.FGSub).1.subschemeι := by
    rw [← Category.assoc, hg₁, Category.assoc, fpT_ι]
  rw [Category.assoc, h₁, ← Category.assoc, ← Category.assoc, fpLiftApp_fpT, ← s.w m]
  rfl

/-- The finitely presented stages have limit `X`. -/
noncomputable def isLimitFpCone : IsLimit (Cone.mk X (fpπ F E)) where
  lift s := F.isLimit.lift (Cone.mk s.pt
    { app := fpLiftApp s
      naturality j j' g := by simpa using (fpLiftApp_map s g).symm })
  fac s c := by
    change _ ≫ F.π.app c.1 ≫ fpT c = _
    rw [← Category.assoc, F.isLimit.fac]
    exact fpLiftApp_fpT s c.1 c.2
  uniq s m hm := by
    refine F.isLimit.hom_ext fun j ↦ ?_
    rw [F.isLimit.fac, ← cancel_mono (E j).e, fpLiftApp_e]
    have h := hm ⟨j, ⊥⟩
    change m ≫ F.π.app j ≫ fpT (⟨j, ⊥⟩ : FPIndex F E) = _ at h
    rw [← h]
    exact congrArg (m ≫ ·) ((congrArg (F.π.app j ≫ ·) (fpT_ι (⟨j, ⊥⟩ : FPIndex F E))).symm.trans
      (Category.assoc _ _ _).symm)

end Scheme.Hom.FiniteApproximation

/-- **An integral morphism is a limit of finite morphisms of finite presentation** (Stacks
Project Tag 09YZ). If `f : X ⟶ S` is integral and `S` is quasi-compact and quasi-separated,
then `X` is a cofiltered limit of schemes finite and of finite presentation over `S`. -/
@[stacks 09YZ]
theorem Scheme.Hom.exists_finiteApproximation_of_isIntegralHom {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIntegralHom f] [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ F : f.FiniteApproximation, ∀ i, LocallyOfFinitePresentation (F.p i) := by
  obtain ⟨F⟩ := f.nonempty_finiteApproximation_of_isIntegralHom
  let E (i : F.I) : (F.p i).ClosedFPEmbedding := (Scheme.Hom.nonempty_closedFPEmbedding _).some
  refine ⟨{
    I := FiniteApproximation.FPIndex F E
    D := FiniteApproximation.fpDiagram F E
    p := FiniteApproximation.fpP
    map_p g := g.2.2
    isFinite_p c := by dsimp [FiniteApproximation.fpP]; infer_instance
    π := FiniteApproximation.fpπ F E
    isLimit := FiniteApproximation.isLimitFpCone
    π_p c := by
      change (F.π.app c.1 ≫ _) ≫ _ = f
      rw [Category.assoc, FiniteApproximation.fpT_fpP, F.π_p] }, fun c ↦ ?_⟩
  dsimp [FiniteApproximation.fpP]
  infer_instance

end AlgebraicGeometry
