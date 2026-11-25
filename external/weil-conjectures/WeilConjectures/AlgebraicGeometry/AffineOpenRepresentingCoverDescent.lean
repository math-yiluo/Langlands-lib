/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
import Mathlib.CategoryTheory.Presentable.Directed
import WeilConjectures.AlgebraicGeometry.EtaleFiniteCoverFactorizationDescent

/-! # Descent of a representing etale cover in an affine open system

Source: Stacks Project, Tags 0EYL and 03Q6, finite objects, maps and cover descent.
(blueprint: lem-weil-pbc-affine-open-representing-cover-descent). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private noncomputable def localizedPullbackIso
    {X S L : Scheme.{u + 1}} (g : S ⟶ X) [Etale g] [Mono g]
    (q : L ⟶ S) (p : L ⟶ X) (hp : q ≫ g = p) (V : S.Etale) :
    p.Etale.obj ((MorphismProperty.Over.map ⊤ (inferInstance : Etale g)).obj V) ≅
      q.Etale.obj V := by
  subst p
  let f := pullback.lift (pullback.fst (V.hom ≫ g) (q ≫ g))
    (pullback.snd (V.hom ≫ g) (q ≫ g))
    ((cancel_mono g).mp (by
      simpa only [Category.assoc] using
        (pullback.condition (f := V.hom ≫ g) (g := q ≫ g))))
  let h : pullback V.hom q ⟶ pullback (V.hom ≫ g) (q ≫ g) :=
    pullback.lift (pullback.fst V.hom q) (pullback.snd V.hom q) (by
      rw [← Category.assoc, pullback.condition, Category.assoc])
  let e : pullback (V.hom ≫ g) (q ≫ g) ≅ pullback V.hom q :=
    ⟨f, h, by apply pullback.hom_ext <;> simp [f, h],
      by apply pullback.hom_ext <;> simp [f, h]⟩
  exact MorphismProperty.Over.isoMk e (by
    change f ≫ pullback.snd V.hom q = pullback.snd (V.hom ≫ g) (q ≫ g)
    exact pullback.lift_snd _ _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem localizedPullbackIso_fst
    {X S L : Scheme.{u + 1}} (g : S ⟶ X) [Etale g] [Mono g]
    (q : L ⟶ S) (p : L ⟶ X) (hp : q ≫ g = p) (V : S.Etale) :
    (localizedPullbackIso g q p hp V).hom.left ≫ pullback.fst V.hom q =
      pullback.fst (V.hom ≫ g) p := by
  subst p
  simp [localizedPullbackIso]

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackComp_fst
    {X Y Z : Scheme.{u + 1}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (p : X ⟶ Z) (hp : p = f ≫ g) (U : Z.Etale) :
    ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      f g p hp).app U).hom.left ≫
        pullback.fst (g.Etale.obj U).hom f ≫ pullback.fst U.hom g =
      pullback.fst U.hom p := by
  subst p
  exact MorphismProperty.Over.pullbackComp_left_fst_fst f g U

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackComp_inv_fst
    {X Y Z : Scheme.{u + 1}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (p : X ⟶ Z) (hp : p = f ≫ g) (U : Z.Etale) :
    ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      f g p hp).app U).inv.left ≫ pullback.fst U.hom p =
        pullback.fst (g.Etale.obj U).hom f ≫ pullback.fst U.hom g := by
  let e := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
    f g p hp).app U
  have hh := congrArg (fun k ↦ k.left) e.inv_hom_id
  change e.inv.left ≫ e.hom.left = 𝟙 _ at hh
  rw [← pullbackComp_fst f g p hp U, ← Category.assoc, ← Category.assoc]
  rw [hh, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Descend a specified finite affine cover and its representing arrows, retaining
one source comparison for both families of arrows.

Source: Stacks Project, Tag 0EYL (finite affine etale site descent), Tag 01ZM
(object and arrow descent), Tag 01ZC(3) (maps to locally finitely presented targets).

Proof: Choose one stage of the nonempty cofiltered diagram, restrict to its
cofiltered tail, and replace that tail by a directed coinitial diagram. The
whiskered cone remains limiting. Its stages are affine, so all its transitions
are affine and all stages are quasi-compact and quasi-separated. Regard the
terminal etale object of the chosen stage as a full affine etale object. Pull
back each U_q to that stage. The structural equation hp and the canonical
pullback-composition isomorphism identify its pullback to the limit with p*U_q.
The pullback of the chosen terminal object is canonically the terminal object
of c.pt. Transport t and b along these comparisons and apply
etale_finiteCoverFactorizationDescent. It descends the affine sources, both
families of arrows under a common source isomorphism, and the covering
condition, to a common later stage. Its auxiliary targets need not be
quasi-compact: maps into them descend by locally finite presentation using
the qcqs base-change diagrams of the affine sources. Identify the later
pullback of the fixed terminal object with the terminal object at that stage.
Compose each stage source structure map with the open immersion of the stage
into X to construct V_q. Compose the descended representing map with the
projection from the pullback of U_q to U_q to construct w_q. Cartesian-square
pasting identifies p*V_q with the limit source; compose this comparison with
the common source isomorphism supplied by descent to obtain d_q. Pullback
extensionality and the representing-arrow equation supplied by descent give
the displayed equality. The stage covering condition is unchanged by the
terminal-object comparison and passage to etale X-objects. If n=0, finite
cover descent makes the terminal object at a later stage empty, yielding
the same conclusion with empty arrow families. -/
private theorem affineOpen_finite_representing_models
    {X : Scheme.{u + 1}} {J : Type (u + 1)} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ X.Etale)
    [∀ j, IsAffine (D.obj j).left] [∀ j, IsOpenImmersion (D.obj j).hom]
    (c : Cone (D ⋙ Scheme.Etale.forget X ⋙ Over.forget X))
    (p : c.pt ⟶ X) (hp : ∀ j, c.π.app j ≫ (D.obj j).hom = p)
    (hc : IsLimit c) (n : ℕ) (T : Fin n → c.pt.Etale)
    (t : ∀ q, T q ⟶ Scheme.Etale.mk (𝟙 c.pt))
    (U : Fin n → X.Etale) (b : ∀ q, T q ⟶ p.Etale.obj (U q))
    (hT : ∀ q, IsAffine (T q).left)
    (ht : Sieve.ofArrows T t ∈
      c.pt.smallEtaleTopology (Scheme.Etale.mk (𝟙 c.pt))) :
    ∃ (j : J) (V : Fin n → X.Etale) (v : ∀ q, V q ⟶ D.obj j)
      (w : ∀ q, V q ⟶ U q) (d : ∀ q, p.Etale.obj (V q) ≅ T q),
      (∀ q, IsAffine (V q).left) ∧
      Sieve.ofArrows V v ∈ X.smallEtaleTopology (D.obj j) ∧
      ∀ q, p.Etale.map (w q) = (d q).hom ≫ b q := by
  classical
  obtain ⟨K, hK, hdir, hne, F, hF⟩ := IsFiltered.exists_directed Jᵒᵖ
  let R := F.leftOp
  have : R.Initial := inferInstance
  let E := R ⋙ D
  let A := E ⋙ Scheme.Etale.forget X ⋙ Over.forget X
  let cc : Cone A := c.whisker R
  have hcc : IsLimit cc := (Functor.Initial.isLimitWhiskerEquiv R c).symm hc
  have (k : Kᵒᵖ) : IsAffine (A.obj k) :=
    inferInstanceAs (IsAffine (D.obj (R.obj k)).left)
  have (k : Kᵒᵖ) : CompactSpace (A.obj k) := inferInstance
  have (k : Kᵒᵖ) : QuasiSeparatedSpace (A.obj k) := inferInstance
  have {k l : Kᵒᵖ} (f : k ⟶ l) : IsAffineHom (A.map f) := inferInstance
  let i₀ : K := Classical.choice hne
  let g := (E.obj (op i₀)).hom
  let q := cc.π.app (op i₀)
  have hqp : q ≫ g = p := hp (R.obj (op i₀))
  let W₀ : (A.obj (op i₀)).FullAffineEtale :=
    ⟨Scheme.Etale.mk (𝟙 _), by change IsAffine (A.obj (op i₀)); infer_instance⟩
  let P := q.Etale
  let e₀ : P.obj W₀.obj ≅ Scheme.Etale.mk (𝟙 c.pt) :=
    (IsTerminal.isTerminalObj P W₀.obj (MorphismProperty.Over.mkIdTerminal @Etale _)).uniqueUpToIso
      (MorphismProperty.Over.mkIdTerminal @Etale _)
  let U₀ := fun x ↦ g.Etale.obj (U x)
  let cmp := fun x ↦ (MorphismProperty.Over.pullbackComp
    (P := @Etale) (Q := ⊤) q g p hqp.symm).app (U x)
  let t₀ := fun x ↦ t x ≫ e₀.inv
  let b₀ := fun x ↦ b x ≫ (cmp x).hom
  have ht₀ : Sieve.ofArrows T t₀ ∈ c.pt.smallEtaleTopology (P.obj W₀.obj) := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff] at ht ⊢
    apply Set.eq_univ_of_forall
    intro x
    have hx : e₀.hom.left x ∈ ⋃ r, Set.range (t r).left := by rw [ht]; trivial
    obtain ⟨r, y, hy⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨r, y, ?_⟩
    change e₀.inv.left ((t r).left y) = x
    rw [hy]
    exact congrArg (fun f ↦ f.left x) e₀.hom_inv_id
  obtain ⟨j, Vj, aj, bj, dj, hcov, hVj, haj, hbj⟩ :=
    etale_finiteCoverFactorizationDescent A cc hcc i₀ W₀ n T t₀ U₀ b₀ ht₀ hT
  let S := E.obj j.left
  let h := cc.π.app j.left
  let s := S.hom
  let f := A.map j.hom
  have hfg : f ≫ g = s := MorphismProperty.Over.w (E.map j.hom)
  have hhs : h ≫ s = p := hp (R.obj j.left)
  have : Etale s := S.prop
  have : Mono s := inferInstanceAs (Mono (D.obj (R.obj j.left)).hom)
  let L := MorphismProperty.Over.map ⊤ (inferInstance : Etale s)
  let cj := fun x ↦ (MorphismProperty.Over.pullbackComp
    (P := @Etale) (Q := ⊤) f g s hfg.symm).app (U x)
  let wj := fun x ↦ bj x ≫ (cj x).inv
  let V := fun x ↦ L.obj (Vj x)
  let v : ∀ x, V x ⟶ S := fun x ↦
    MorphismProperty.Over.homMk (Vj x).hom rfl
  let w : ∀ x, V x ⟶ U x := fun x ↦ L.map (wj x) ≫
    MorphismProperty.Over.homMk (pullback.fst (U x).hom s) (pullback.condition)
  let d := fun x ↦ localizedPullbackIso s h p hhs (Vj x) ≪≫ dj x
  refine ⟨R.obj j.left, V, v, w, d, hVj, ?_, ?_⟩
  · let tj : IsTerminal (Scheme.Etale.mk (𝟙 (A.obj j.left))) :=
      MorphismProperty.Over.mkIdTerminal @Etale _
    let ej := (IsTerminal.isTerminalObj f.Etale W₀.obj
      (MorphismProperty.Over.mkIdTerminal @Etale _)).uniqueUpToIso tj
    have heq (x : Fin n) : aj x ≫ ej.hom =
        MorphismProperty.Over.homMk (Vj x).hom := tj.hom_ext _ _
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff] at hcov ⊢
    apply Set.eq_univ_of_forall
    intro x
    have hx : ej.inv.left x ∈ ⋃ r, Set.range (aj r).left := by rw [hcov]; trivial
    obtain ⟨r, y, hy⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨r, y, ?_⟩
    have he := congrArg (fun k ↦ k.left y) (heq r)
    change ej.hom.left ((aj r).left y) = (Vj r).hom y at he
    change (Vj r).hom y = x
    rw [← he, hy]
    exact congrArg (fun k ↦ k.left x) ej.inv_hom_id
  · intro x
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · have hh := congrArg (fun k ↦ k.left ≫
          pullback.fst (U₀ x).hom q ≫ pullback.fst (U x).hom g) (hbj x)
      simp only [MorphismProperty.Comma.comp_left, Category.assoc] at hh
      dsimp only [w, wj, V, L, d, Iso.trans_hom]
      simp only [Category.assoc]
      rw [Scheme.Hom.etale_map_left_comp_fst]
      have hcmp := pullbackComp_fst q g p hqp.symm (U x)
      have hcj := pullbackComp_inv_fst f g s hfg.symm (U x)
      have hej := pullbackComp_inv_fst h f q (cc.w j.hom).symm (U₀ x)
      have hmap : (h.Etale.map (bj x)).left ≫
          pullback.fst (f.Etale.obj (U₀ x)).hom h =
          pullback.fst (Vj x).hom h ≫ (bj x).left :=
        Scheme.Hom.etale_map_left_comp_fst h (bj x)
      have hloc := localizedPullbackIso_fst s h p hhs (Vj x)
      change (h.Etale.map (bj x)).left ≫
        (((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
          h f q (cc.w j.hom).symm).app (U₀ x)).inv).left ≫
        pullback.fst (U₀ x).hom q ≫ pullback.fst (U x).hom g =
        (dj x).hom.left ≫ (b x).left ≫ (cmp x).hom.left ≫
          pullback.fst (U₀ x).hom q ≫ pullback.fst (U x).hom g at hh
      change (cmp x).hom.left ≫ pullback.fst (U₀ x).hom q ≫
        pullback.fst (U x).hom g = pullback.fst (U x).hom p at hcmp
      change (cj x).inv.left ≫ pullback.fst (U x).hom s =
        pullback.fst (U₀ x).hom f ≫ pullback.fst (U x).hom g at hcj
      rw [reassoc_of% hej, reassoc_of% hmap, hcmp] at hh
      change pullback.fst ((Vj x).hom ≫ s) p ≫
          (bj x).left ≫ (cj x).inv.left ≫ pullback.fst (U x).hom s =
        (localizedPullbackIso s h p hhs (Vj x)).hom.left ≫
          (dj x).hom.left ≫ (b x).left ≫ pullback.fst (U x).hom p
      rw [hcj, ← hloc]
      simpa only [Category.assoc] using
        congrArg (fun k ↦ (localizedPullbackIso s h p hhs (Vj x)).hom.left ≫ k) hh
    · simp only [Scheme.Hom.etale_map_left_comp_snd]
      exact (MorphismProperty.Over.w ((d x).hom ≫ b x)).symm

/-- Refine a covering with representing maps and descend its geometric data.
Source: Stacks Project, Tag 0EYL, finite diagram and finite cover descent;
Tag 03Q6, proof steps (1)--(3); Tag 01ZM, morphism descent.
(blueprint: lem-weil-pbc-affine-open-representing-cover-descent).

Proof: Fix one affine open stage and reindex its cofiltered tail by a
directed coinitial system. The limit is affine. Refine the Z-cover by a finite
affine etale cover, retaining each source's map to a selected Z_i and hence
its representing arrow to p^*W_i. Use the terminal etale object at the fixed
stage as the fixed affine target. Pull back each W_i to that stage; these
etale objects need not be quasi-compact. Canonical pullback comparisons and
p = (limit projection) followed by (stage immersion) convert the finite
covering maps and representing arrows into the input of
etale_finiteCoverFactorizationDescent. It descends affine sources and both
families of maps to a common later stage, makes the stage family covering,
and retains the equations under one common source comparison. Its proof
uses the base-change diagram of each affine source model and locally finite
presentation of W_i to descend representing maps, so no quasi-compactness
of W_i or X is imposed. Identify the stage pullback of the fixed terminal
object with the stage terminal object. Compose model structure maps with
the stage immersion to obtain the X-objects V_b. Compose representing maps
with the pullback projections to obtain w_b, and the source comparisons
with the original refinement maps to obtain e_b. Pullback hom_ext proves
p^*(w_b)=e_b followed by a_{r(b)}. The composites with z_{r(b)} recover the
refining limit cover, and the stage covering property survives terminal
comparison and composition into X. For an empty limit the same finite
cover descent makes an empty stage. No sheaves or sections are involved. -/
theorem affineOpen_representing_cover_descent
    {X : Scheme.{u + 1}} {J : Type (u + 1)} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ X.Etale)
    [∀ j, IsAffine (D.obj j).left] [∀ j, IsOpenImmersion (D.obj j).hom]
    (c : Cone (D ⋙ Scheme.Etale.forget X ⋙ Over.forget X))
    (p : c.pt ⟶ X) (hp : ∀ j, c.π.app j ≫ (D.obj j).hom = p)
    (hc : IsLimit c)
    (I : Type (u + 1)) (Z : I → c.pt.Etale)
    (z : ∀ i, Z i ⟶ Scheme.Etale.mk (𝟙 c.pt))
    (W : I → X.Etale) (a : ∀ i, Z i ⟶ p.Etale.obj (W i))
    (hz : Sieve.ofArrows Z z ∈
      c.pt.smallEtaleTopology (Scheme.Etale.mk (𝟙 c.pt))) :
    ∃ (j : J) (B : Type (u + 1)) (_ : Finite B) (r : B → I)
      (V : B → X.Etale) (v : ∀ b, V b ⟶ D.obj j)
      (w : ∀ b, V b ⟶ W (r b)) (e : ∀ b, p.Etale.obj (V b) ⟶ Z (r b)),
      (∀ b, IsAffine (V b).left) ∧
      Sieve.ofArrows V v ∈ X.smallEtaleTopology (D.obj j) ∧
      Sieve.ofArrows (fun b ↦ p.Etale.obj (V b)) (fun b ↦ e b ≫ z (r b)) ∈
        c.pt.smallEtaleTopology (Scheme.Etale.mk (𝟙 c.pt)) ∧
      ∀ b, p.Etale.map (w b) = e b ≫ a (r b) := by
  classical
  have (j : J) : IsAffine ((D ⋙ Scheme.Etale.forget X ⋙ Over.forget X).obj j) :=
    inferInstanceAs (IsAffine (D.obj j).left)
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have : CompactSpace (Scheme.Etale.mk (𝟙 c.pt)).left :=
    inferInstanceAs (CompactSpace c.pt)
  obtain ⟨n, T, t, hmem, hT, ht⟩ :=
    (AlgebraicGeometry.Etale.exists_affine_refinement _) hz
  have hfactor (q : Fin n) : ∃ (i : I) (f : T q ⟶ Z i), t q = f ≫ z i :=
    Sieve.ofArrows.exists (hmem q)
  choose r f hf using hfactor
  obtain ⟨j, V, v, w, d, hV, hv, hw⟩ :=
    affineOpen_finite_representing_models D c p hp hc n T t
      (fun q ↦ W (r q)) (fun q ↦ f q ≫ a (r q)) hT
      ((Scheme.ofArrows_mem_smallEtaleTopology_iff t).mpr ht)
  let B := ULift.{u + 1} (Fin n)
  refine ⟨j, B, inferInstance, (fun q ↦ r q.down), (fun q ↦ V q.down),
    (fun q ↦ v q.down), (fun q ↦ w q.down),
    (fun q ↦ (d q.down).hom ≫ f q.down), (fun q ↦ hV q.down), ?_, ?_, ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff] at hv ⊢
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ q, Set.range (v q).left := by rw [hv]; trivial
    obtain ⟨q, y, hy⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨ULift.up q, y, hy⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ q, Set.range (t q).left := by rw [ht]; trivial
    obtain ⟨q, y, hy⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨ULift.up q, (d q).inv.left y, ?_⟩
    have hid := congrArg (fun g ↦ g.left y) (d q).inv_hom_id
    change (d q).hom.left ((d q).inv.left y) = y at hid
    change (z (r q)).left ((f q).left ((d q).hom.left ((d q).inv.left y))) = x
    rw [hid]
    have htf := congrArg (fun g ↦ g.left y) (hf q)
    exact htf.symm.trans hy
  · intro q
    simpa only [Category.assoc] using hw q.down
