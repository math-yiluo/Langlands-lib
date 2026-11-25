/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleVanishingLocus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Rigidity of sections of pulled back étale sheaves

Let `t : T ⟶ R` be a morphism of schemes and `G` an abelian étale sheaf on `R`.

If `t` factors through the spectrum of a separably closed field `Ω`, then the vanishing locus
of every section of `t^* G` is closed (and open): étale locally such a section is the pullback
of a section of the pullback of `G` to `Spec Ω`, and the latter vanishes as soon as it vanishes
at the unique point of `Spec Ω`
(`AlgebraicGeometry.Etale.isClosed_vanishingLocus_of_eq_comp`).

As a consequence, for a geometrically connected `q : T ⟶ X` with a section `σ`, a section of
`q^* G` over the base change of `X` which vanishes along `σ` vanishes, since its restriction
to every geometric fibre of `q` is a section with clopen and nonempty vanishing locus on a
connected scheme (`AlgebraicGeometry.Etale.eq_zero_of_restrictAlong_eq_zero_of_section`).
Hence the pullback map on sections along `q` is surjective
(`AlgebraicGeometry.Etale.surjective_unit_app_of_section`); it is injective as soon as `q`
is surjective (`AlgebraicGeometry.Etale.injective_unit_app_of_surjective`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

section RestrictAlong

variable {R T T' : Scheme.{u}} (t : T ⟶ R) (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
  (f : T' ⟶ T) (t' : T' ⟶ R) (ht' : t' = f ≫ t)

/-- The vanishing locus of the restriction of `s` along `m` is contained in the preimage of
the vanishing locus of `s`. -/
lemma vanishingLocus_restrictAlong_subset {V : T.Etale} {V' : T'.Etale}
    (m : V'.left ⟶ V.left) (hm : m ≫ V.hom = V'.hom ≫ f)
    (s : ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op V)) :
    vanishingLocus _ (restrictAlong t G f t' ht' m hm s) ⊆
      m ⁻¹' vanishingLocus ((t)^*[AddCommGrpCat.{u + 1}].obj G) s := by
  rintro _ ⟨W, b, ⟨w, rfl⟩, hb⟩
  rw [map_restrictAlong] at hb
  have := range_subset_vanishingLocus_of_restrictAlong_eq_zero t G f t' ht' _ _ s hb ⟨w, rfl⟩
  simpa using this

/-- `restrictAlong` only depends on the morphism `f`, not on its presentation. -/
lemma restrictAlong_congr_left {f₁ f₂ : T' ⟶ T} (hf : f₁ = f₂) (ht₁ : t' = f₁ ≫ t)
    {V : T.Etale} {V' : T'.Etale} (m : V'.left ⟶ V.left) (hm : m ≫ V.hom = V'.hom ≫ f₁) :
    restrictAlong t G f₁ t' ht₁ m hm = restrictAlong t G f₂ t' (hf ▸ ht₁) m (hf ▸ hm) := by
  subst hf
  rfl

end RestrictAlong

section SepClosed

variable {R T : Scheme.{u}} (t : T ⟶ R) (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (g : T ⟶ Spec (.of Ω)) (h : Spec (.of Ω) ⟶ R)
  (hgh : t = g ≫ h)

set_option backward.isDefEq.respectTransparency false in
include hgh in
/-- **Vanishing loci over a geometric point are closed.** If `t : T ⟶ R` factors through the
spectrum of a separably closed field, then the vanishing locus of every section of `t^* G`
is closed. Étale locally around a point, such a section is the restriction of a section of
the pullback of `G` to `Spec Ω`, which vanishes as soon as it vanishes somewhere. -/
lemma isClosed_vanishingLocus_of_eq_comp {V : T.Etale}
    (s : ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op V)) :
    IsClosed (vanishingLocus _ s) := by
  rw [← closure_subset_iff_isClosed]
  intro z hz
  obtain ⟨V₁, e, U, φ, hφ, c, ⟨v₀, hv₀⟩, hs⟩ := exists_pullSection_eq t G s z
  have : AlgebraicGeometry.Etale U.hom := U.prop
  let φ' : V₁.left ⟶ pullback U.hom h :=
    pullback.lift φ (V₁.hom ≫ g) (by rw [hφ, hgh, Category.assoc])
  obtain ⟨l, hl, hlv⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (pullback.snd U.hom h)
    (𝟙 _) (φ' v₀) (Subsingleton.elim _ _)
  -- the étale `Spec Ω`-schemes `U ×_R Spec Ω` and `Spec Ω`
  let P : (Spec (.of Ω)).Etale := Scheme.Etale.mk (pullback.snd U.hom h)
  let O : (Spec (.of Ω)).Etale := Scheme.Etale.mk (𝟙 (Spec (.of Ω)))
  let la : O ⟶ P := MorphismProperty.Over.homMk l hl
  let lam : Spec (.of Ω) ⟶ U.left := l ≫ pullback.fst U.hom h
  have hlam : lam ≫ U.hom = O.hom ≫ h := by
    simp only [lam, Category.assoc, pullback.condition, O]
    rw [reassoc_of% hl]
    exact (Category.id_comp h).symm
  let c' := pullSection h G (V := O) lam hlam c
  let V₂ : T.Etale := pullbackObj (V := P) φ' la
  let b : V₂ ⟶ V := pullbackObjFst (V := P) φ' la ≫ e
  have hm : pullback.snd φ' la.left ≫ O.hom = V₂.hom ≫ g := by
    change pullback.snd φ' l ≫ 𝟙 _ = (pullback.fst φ' l ≫ V₁.hom) ≫ g
    rw [Category.comp_id, Category.assoc, ← pullback.lift_snd φ (V₁.hom ≫ g)
      (by rw [hφ, hgh, Category.assoc]), ← Category.assoc]
    change _ = (pullback.fst φ' l ≫ φ') ≫ _
    rw [pullback.condition, Category.assoc, hl, Category.comp_id]
  -- the restriction of `s` to `V₂` is the restriction of `c'`
  have hs₂ : ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.map b.op s =
      restrictAlong h G g t hgh (V := O) (V' := V₂) (pullback.snd φ' la.left) hm c' := by
    rw [restrictAlong_pullSection, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hs,
      map_pullSection]
    apply pullSection_congr
    change pullback.fst φ' l ≫ φ = pullback.snd φ' l ≫ l ≫ pullback.fst U.hom h
    rw [← pullback.condition_assoc]
    simp [φ']
  -- `c'` vanishes as soon as the restriction of `s` to `V₂` vanishes somewhere
  have key : (vanishingLocus _ (((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.map b.op s)).Nonempty →
      ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.map b.op s = 0 := by
    rintro ⟨w, hw⟩
    rw [hs₂] at hw ⊢
    have hc : c' = 0 := by
      refine eq_zero_of_forall_mem_vanishingLocus fun x ↦ ?_
      have := vanishingLocus_restrictAlong_subset h G g t hgh _ hm c' hw
      rwa [show x = pullback.snd φ' la.left w from Subsingleton.elim (α := Spec (.of Ω)) _ _]
    rw [hc, map_zero]
  -- a point of `V₂` over `z`
  obtain ⟨w₀, hw₀, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ') (g := la.left) v₀
    (default : Spec (.of Ω)) hlv.symm
  have hz' : z = b.left w₀ := by
    change z = e.left (pullback.fst φ' la.left w₀)
    rw [hw₀, hv₀]
  -- the image of `V₂` is an open neighbourhood of `z` meeting the vanishing locus of `s`
  obtain ⟨_, ⟨w, rfl⟩, hw⟩ := mem_closure_iff.1 hz _ b.left.isOpenMap.isOpen_range ⟨w₀, hz'.symm⟩
  have h₀ := key ⟨w, by rw [vanishingLocus_map]; exact hw⟩
  rw [hz']
  exact mem_vanishingLocus_of_map_eq_zero b h₀ w₀

end SepClosed

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

section Unit

variable {R T : Scheme.{u}} (t : T ⟶ R) (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The unit `G ⟶ t_* t^* G` sends a section `g` over `W` to its pullback along the projection
`W ×_R T ⟶ W`. -/
lemma unit_app_hom_app_eq_pullSection (W : R.Etale) (g : G.obj.obj (op W)) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app G).hom.app (op W) g =
      pullSection t G (V := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ t).obj W)
        (pullback.fst W.hom t) pullback.condition g := by
  have := map_unit_app_eq_pullSection t G (𝟙 _) g
  rw [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] at this
  refine this.trans ?_
  apply pullSection_congr
  simp

/-- **Pullback of sections along a surjective morphism is injective.** -/
lemma injective_unit_app_of_surjective [Surjective t] (W : R.Etale) :
    Function.Injective
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app G).hom.app (op W)) := by
  intro g₁ g₂ hg
  rw [← sub_eq_zero, ← map_sub, unit_app_hom_app_eq_pullSection] at hg
  rw [← sub_eq_zero]
  have h₁ := range_subset_vanishingLocus_of_pullSection_eq_zero t G _ _ _ hg
  have : Surjective (pullback.fst W.hom t) :=
    MorphismProperty.pullback_fst (P := @Surjective) _ _ ‹_›
  exact eq_zero_of_forall_mem_vanishingLocus fun x ↦ h₁ ((pullback.fst W.hom t).surjective x)

end Unit

section Section

variable {X T : Scheme.{u}} (q : T ⟶ X) (σ : X ⟶ T) (hσ : σ ≫ q = 𝟙 X)
  (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

set_option backward.isDefEq.respectTransparency false in
/-- **Rigidity.** Let `q : T ⟶ X` be geometrically connected with a section `σ`. A section `s`
of `q^* G` over the base change `V` of `X` (that is, `V ⟶ T` an isomorphism) which vanishes
along `σ` vanishes. On the geometric fibre of `q` through a point of `V`, the vanishing locus
of the restriction of `s` is open, closed
(`AlgebraicGeometry.Etale.isClosed_vanishingLocus_of_eq_comp`) and contains the point coming
from `σ`, hence is everything since the fibre is connected. -/
lemma eq_zero_of_restrictAlong_eq_zero_of_section [GeometricallyConnected q] {V : T.Etale}
    [IsIso V.hom] {V' : X.Etale} [IsIso V'.hom] (m : V'.left ⟶ V.left)
    (hm : m ≫ V.hom = V'.hom ≫ σ) (s : ((q)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op V))
    (hs : restrictAlong q G σ (𝟙 X) hσ.symm m hm s = 0) : s = 0 := by
  refine eq_zero_of_forall_mem_vanishingLocus fun y ↦ ?_
  -- the geometric fibre `Z` of `q` through `y`
  let x := q (V.hom y)
  let xb := X.algClosurePoint x
  let f := pullback.fst q xb
  let g := pullback.snd q xb
  have : ConnectedSpace ↥(pullback q xb) :=
    GeometricallyConnected.geometrically_connectedSpace (f := q) xb f g
      (IsPullback.of_hasPullback _ _)
  let VZ := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).obj V
  have : IsIso VZ.hom := (inferInstance : IsIso (pullback.snd V.hom f))
  have : ConnectedSpace VZ.left := VZ.hom.homeomorph.connectedSpace_iff.mpr ‹_›
  have hmZ : pullback.fst V.hom f ≫ V.hom = VZ.hom ≫ f := pullback.condition
  -- the restriction `E` of `s` to the fibre has clopen vanishing locus
  have hcl := isClosed_vanishingLocus_of_eq_comp (f ≫ q) G g xb pullback.condition
    (restrictAlong q G f (f ≫ q) rfl (V' := VZ) (pullback.fst V.hom f) hmZ s)
  have hop := isOpen_vanishingLocus
    (restrictAlong q G f (f ≫ q) rfl (V' := VZ) (pullback.fst V.hom f) hmZ s)
  -- `E` vanishes along the section of the fibre induced by `σ`
  let σZ : Spec (.of (AlgebraicClosure (X.residueField x))) ⟶ pullback q xb :=
    pullback.lift (xb ≫ σ) (𝟙 _) (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  have hσZ : σZ ≫ f = xb ≫ σ := pullback.lift_fst _ _ _
  let V'' := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ σZ).obj VZ
  have : IsIso V''.hom := (inferInstance : IsIso (pullback.snd VZ.hom σZ))
  have hm'' : pullback.fst VZ.hom σZ ≫ VZ.hom = V''.hom ≫ σZ := pullback.condition
  let n : V''.left ⟶ V'.left := V''.hom ≫ xb ≫ inv V'.hom
  have hn : n ≫ V'.hom = V''.hom ≫ xb := by simp [n]
  have hnm : pullback.fst VZ.hom σZ ≫ pullback.fst V.hom f = n ≫ m := by
    rw [← cancel_mono V.hom, Category.assoc, hmZ, reassoc_of% hm'', hσZ, Category.assoc, hm]
    simp [n]
  have hE : restrictAlong (f ≫ q) G σZ xb (by rw [reassoc_of% hσZ, hσ, Category.comp_id])
      (V := VZ) (V' := V'') (pullback.fst VZ.hom σZ) hm''
        (restrictAlong q G f (f ≫ q) rfl (V' := VZ) (pullback.fst V.hom f) hmZ s) = 0 := by
    rw [restrictAlong_restrictAlong, restrictAlong_congr_left q G xb hσZ,
      restrictAlong_congr (h := hnm), ← restrictAlong_restrictAlong q G σ (𝟙 X) hσ.symm xb xb
        (Category.comp_id _).symm m hm n hn, hs, map_zero]
  have hne := range_subset_vanishingLocus_of_restrictAlong_eq_zero (f ≫ q) G σZ xb _ _ hm'' _ hE
    ⟨inv V''.hom (default : Spec (.of (AlgebraicClosure (X.residueField x)))), rfl⟩
  have huniv := IsClopen.eq_univ ⟨hcl, hop⟩ ⟨_, hne⟩
  rw [← eq_zero_iff_vanishingLocus_eq_univ] at huniv
  -- every point of `V` lies on such a fibre
  have h₁ := range_subset_vanishingLocus_of_restrictAlong_eq_zero q G f (f ≫ q) rfl _ hmZ s huniv
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := xb) (V.hom y)
    (default : Spec (.of (AlgebraicClosure (X.residueField x))))
    (X.algClosurePoint_base x _).symm
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := V.hom) (g := f) y z hz.symm
  exact h₁ ⟨w, hw⟩

/-- Pullback along an isomorphism `𝟙 X` is bijective on sections. -/
lemma bijective_unit_app_id (W : X.Etale) :
    Function.Bijective
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (𝟙 X)).unit.app G).hom.app (op W)) := by
  have := isEquivalence_upperStar AddCommGrpCat.{u + 1} (𝟙 X)
  have : IsIso ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (𝟙 X)).unit.app G) :=
    inferInstance
  exact ConcreteCategory.bijective_of_isIso
    (((sheafSections _ _).obj (op W)).map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (𝟙 X)).unit.app G))

include hσ in
/-- **Pullback of sections along a geometrically connected morphism with a section is
surjective** over every `W` étale over `X` whose structure morphism is an isomorphism. -/
lemma surjective_unit_app_of_section [GeometricallyConnected q] (W : X.Etale) [IsIso W.hom] :
    Function.Surjective
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} q).unit.app G).hom.app (op W)) := by
  intro s
  obtain ⟨s₀, hs₀⟩ := (bijective_unit_app_id G W).2
    ((unitComparison σ q (𝟙 X) hσ.symm G).hom.app (op W) s)
  refine ⟨s₀, ?_⟩
  rw [← sub_eq_zero]
  have : IsIso ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ q).obj W).hom :=
    (inferInstance : IsIso (pullback.snd W.hom q))
  have : IsIso ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ (𝟙 X)).obj W).hom :=
    (inferInstance : IsIso (pullback.snd W.hom (𝟙 X)))
  refine eq_zero_of_restrictAlong_eq_zero_of_section q σ hσ G
    (V := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ q).obj W)
    (V' := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ (𝟙 X)).obj W)
    (pullback.map W.hom (𝟙 X) W.hom q (𝟙 _) σ (𝟙 _) (by simp) (by simp [hσ]))
    (pullback.lift_snd _ _ _) _ ?_
  rw [← unitComparison_hom_app_eq, map_sub, sub_eq_zero]
  refine Eq.trans ?_ hs₀
  exact congrArg (fun φ ↦ φ.hom.app (op W) s₀) (unit_app_comp_unitComparison σ q (𝟙 X) hσ.symm G)

end Section

end AlgebraicGeometry.Etale
