import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationSchemeQuotient
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationInvariantOpenDescent
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationCartesianAffineQuotientProof
import Langlands.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeSourceDescentProof
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Maps and limits of scheme quotients of étale equivalence relations

A scheme quotient `Q` of an étale equivalence relation `F` (an étale surjection `q : F.U ⟶ M`
with kernel pair `F.R`) is an effective epimorphism, so morphisms out of `M` are morphisms out of
`F.U` that are constant on related points. A cartesian morphism `(f, g) : E' ⟶ E` therefore
induces a morphism of quotients, and the square formed by `f`, the two quotient maps and the
induced morphism is cartesian. Over an open `V` of `M` the restriction of `q` is a quotient of the
chart relation on `q⁻¹ V`; this identifies the affine opens of `M` with the invariant opens of
`F.U` whose chart relations have affine quotients. Consequently quotients pull back along
cartesian morphisms with affine object map, and the induced maps of quotients are affine.

For a cofiltered diagram of cartesian morphisms whose object schemes have the cone point as limit,
the quotients form a diagram whose limit is the quotient of the cone point. This is the scheme
form of the statement that a limit of algebraic spaces along affine transition maps is computed
on étale presentations (Stacks Project, Lemma 70.4.1, Tag 07SF, and its use in Proposition
70.8.1, Tag 07SU).
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

/-- A commutative square of schemes is a pullback when lifts are unique and exist after
precomposition with an effective epimorphism. -/
lemma isPullback_of_exists_local {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (w : fst ≫ f = snd ≫ g)
    (hom_ext : ∀ ⦃T : Scheme.{u}⦄ ⦃φ φ' : T ⟶ P⦄, φ ≫ fst = φ' ≫ fst →
      φ ≫ snd = φ' ≫ snd → φ = φ')
    (exists_local : ∀ ⦃T : Scheme.{u}⦄ (a : T ⟶ X) (b : T ⟶ Y), a ≫ f = b ≫ g →
      ∃ (T₁ : Scheme.{u}) (e : T₁ ⟶ T) (d : T₁ ⟶ P),
        EffectiveEpi e ∧ d ≫ fst = e ≫ a ∧ d ≫ snd = e ≫ b) :
    IsPullback fst snd f g := by
  refine IsPullback.mk' w hom_ext ?_
  intro T a b hab
  obtain ⟨T₁, e, d, he, hda, hdb⟩ := exists_local a b hab
  have hd : ∀ {W : Scheme.{u}} (g₁ g₂ : W ⟶ T₁), g₁ ≫ e = g₂ ≫ e → g₁ ≫ d = g₂ ≫ d := by
    intro W g₁ g₂ h
    apply hom_ext
    · rw [Category.assoc, Category.assoc, hda, ← Category.assoc, h, Category.assoc]
    · rw [Category.assoc, Category.assoc, hdb, ← Category.assoc, h, Category.assoc]
  refine ⟨EffectiveEpi.desc e d hd, ?_, ?_⟩
  · rw [← cancel_epi e, ← Category.assoc, EffectiveEpi.fac, hda]
  · rw [← cancel_epi e, ← Category.assoc, EffectiveEpi.fac, hdb]

/-- Two effective epimorphisms with the same kernel pair square have isomorphic targets,
compatibly with the two epimorphisms. -/
lemma exists_iso_of_isPullback {R X Y Y' : Scheme.{u}} {t s : R ⟶ X} {q : X ⟶ Y}
    {q' : X ⟶ Y'} [EffectiveEpi q] [EffectiveEpi q'] (h : IsPullback t s q q)
    (h' : IsPullback t s q' q') : ∃ e : Y ≅ Y', q ≫ e.hom = q' := by
  have H : ∀ {q₁ : X ⟶ Y} {q₂ : X ⟶ Y'} (_ : IsPullback t s q₁ q₁) (_ : IsPullback t s q₂ q₂)
      {W : Scheme.{u}} (g₁ g₂ : W ⟶ X), g₁ ≫ q₁ = g₂ ≫ q₁ → g₁ ≫ q₂ = g₂ ≫ q₂ := by
    intro q₁ q₂ h₁ h₂ W g₁ g₂ hg
    obtain ⟨r, hr1, hr2⟩ : ∃ r, r ≫ t = g₁ ∧ r ≫ s = g₂ :=
      ⟨_, h₁.lift_fst _ _ hg, h₁.lift_snd _ _ hg⟩
    rw [← hr1, ← hr2, Category.assoc, Category.assoc, h₂.w]
  have H' : ∀ {q₁ : X ⟶ Y'} {q₂ : X ⟶ Y} (_ : IsPullback t s q₁ q₁) (_ : IsPullback t s q₂ q₂)
      {W : Scheme.{u}} (g₁ g₂ : W ⟶ X), g₁ ≫ q₁ = g₂ ≫ q₁ → g₁ ≫ q₂ = g₂ ≫ q₂ := by
    intro q₁ q₂ h₁ h₂ W g₁ g₂ hg
    obtain ⟨r, hr1, hr2⟩ : ∃ r, r ≫ t = g₁ ∧ r ≫ s = g₂ :=
      ⟨_, h₁.lift_fst _ _ hg, h₁.lift_snd _ _ hg⟩
    rw [← hr1, ← hr2, Category.assoc, Category.assoc, h₂.w]
  let φ : Y ⟶ Y' := EffectiveEpi.desc q q' (H h h')
  let ψ : Y' ⟶ Y := EffectiveEpi.desc q' q (H' h' h)
  have hφ : q ≫ φ = q' := EffectiveEpi.fac _ _ _
  have hψ : q' ≫ ψ = q := EffectiveEpi.fac _ _ _
  refine ⟨⟨φ, ψ, ?_, ?_⟩, hφ⟩
  · rw [← cancel_epi q, ← Category.assoc, hφ, hψ, Category.comp_id]
  · rw [← cancel_epi q', ← Category.assoc, hψ, hφ, Category.comp_id]

namespace SchemeQuotient

section Basic

variable {F : EtaleEquivalenceRelation.{u}} (Q : F.SchemeQuotient)

@[reassoc]
lemma w : F.t ≫ Q.q = F.s ≫ Q.q := Q.isPullback.w

instance : EffectiveEpi Q.q := inferInstance

/-- Points of the object scheme with the same image in the quotient have the same image under
any morphism that is constant on related points. -/
lemma comp_eq_of_comp_q_eq {W : Scheme.{u}} {g : F.U ⟶ W} (hg : F.t ≫ g = F.s ≫ g)
    {T : Scheme.{u}} (a b : T ⟶ F.U) (h : a ≫ Q.q = b ≫ Q.q) : a ≫ g = b ≫ g := by
  obtain ⟨r, hr1, hr2⟩ : ∃ r, r ≫ F.t = a ∧ r ≫ F.s = b :=
    ⟨_, Q.isPullback.lift_fst _ _ h, Q.isPullback.lift_snd _ _ h⟩
  rw [← hr1, ← hr2, Category.assoc, Category.assoc, hg]

/-- The morphism out of the quotient induced by a morphism constant on related points. -/
noncomputable def desc {W : Scheme.{u}} (g : F.U ⟶ W) (hg : F.t ≫ g = F.s ≫ g) : Q.M ⟶ W :=
  EffectiveEpi.desc Q.q g (fun a b h => Q.comp_eq_of_comp_q_eq hg a b h)

@[reassoc (attr := simp)]
lemma fac {W : Scheme.{u}} (g : F.U ⟶ W) (hg : F.t ≫ g = F.s ≫ g) : Q.q ≫ Q.desc g hg = g :=
  EffectiveEpi.fac _ _ _

lemma hom_ext {W : Scheme.{u}} {a b : Q.M ⟶ W} (h : Q.q ≫ a = Q.q ≫ b) : a = b :=
  (cancel_epi Q.q).1 h

/-- The inverse image of an open of the quotient is invariant. -/
lemma isInvariantOpen_preimage (V : Q.M.Opens) : F.IsInvariantOpen (Q.q ⁻¹ᵁ V) := by
  change F.s ⁻¹ᵁ (Q.q ⁻¹ᵁ V) = F.t ⁻¹ᵁ (Q.q ⁻¹ᵁ V)
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, Q.w]

/-- Over an open `V` of the quotient, the restriction of the quotient map is a quotient of
the chart relation on `q⁻¹ V`. -/
lemma isPullback_chart_restrict (V : Q.M.Opens) :
    IsPullback (Chart.t F (Q.q ⁻¹ᵁ V).ι) (Chart.s F (Q.q ⁻¹ᵁ V).ι) (Q.q ∣_ V) (Q.q ∣_ V) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · rw [← cancel_mono V.ι]
    simp only [Category.assoc, morphismRestrict_ι]
    rw [← Chart.map_t_assoc, ← Chart.map_s_assoc, Q.w]
  · intro T φ φ' ht hs
    exact Chart.hom_ext F _ ht hs
  · intro T a b hab
    have h' : (a ≫ (Q.q ⁻¹ᵁ V).ι) ≫ Q.q = (b ≫ (Q.q ⁻¹ᵁ V).ι) ≫ Q.q := by
      simp only [Category.assoc, ← morphismRestrict_ι]
      rw [reassoc_of% hab]
    exact ⟨Chart.lift F _ a b (Q.isPullback.lift _ _ h') (Q.isPullback.lift_fst _ _ _)
      (Q.isPullback.lift_snd _ _ _), Chart.lift_t _ _ _ _ _ _ _, Chart.lift_s _ _ _ _ _ _ _⟩

/-- Over an affine open `V` of the quotient, the chart relation on `q⁻¹ V` has the affine
quotient `V`. -/
theorem hasAffineQuotient_chart (V : Q.M.Opens) (hV : IsAffineOpen V) :
    (F.chart (Q.q ⁻¹ᵁ V).ι).HasAffineQuotient :=
  ⟨V, Q.q ∣_ V, hV, Q.isPullback_chart_restrict V,
    MorphismProperty.of_isPullback (P := @Flat) (isPullback_morphismRestrict Q.q V).flip inferInstance,
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (isPullback_morphismRestrict Q.q V).flip inferInstance,
    MorphismProperty.of_isPullback (P := @Surjective)
      (isPullback_morphismRestrict Q.q V).flip inferInstance⟩

/-- An open of the quotient whose inverse image carries a chart relation with an affine quotient
is affine. -/
theorem isAffineOpen_of_hasAffineQuotient_chart (W : Q.M.Opens)
    (h : (F.chart (Q.q ⁻¹ᵁ W).ι).HasAffineQuotient) : IsAffineOpen W := by
  obtain ⟨M', q', hM', hpb, hflat, hlfp, hsurj⟩ := h
  have : Flat (Q.q ∣_ W) :=
    MorphismProperty.of_isPullback (P := @Flat) (isPullback_morphismRestrict Q.q W).flip inferInstance
  have : LocallyOfFinitePresentation (Q.q ∣_ W) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (isPullback_morphismRestrict Q.q W).flip inferInstance
  have : Surjective (Q.q ∣_ W) :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (isPullback_morphismRestrict Q.q W).flip inferInstance
  obtain ⟨e, -⟩ := exists_iso_of_isPullback (Q.isPullback_chart_restrict W) hpb
  exact IsAffine.of_isIso e.hom

/-- The inverse image of the image of an invariant open is the open itself. -/
lemma preimage_image_eq {V : F.U.Opens} (hV : F.IsInvariantOpen V) :
    Q.q ⁻¹' (Q.q '' (V : Set F.U)) = V := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := Q.q) (g := Q.q) x y
      hxy.symm
    let r := Q.isPullback.isoPullback.inv z
    have hrt : F.t r = x := by
      rw [← hz₁]
      change (Q.isPullback.isoPullback.inv ≫ F.t) z = _
      rw [IsPullback.isoPullback_inv_fst]
    have hrs : F.s r = y := by
      rw [← hz₂]
      change (Q.isPullback.isoPullback.inv ≫ F.s) z = _
      rw [IsPullback.isoPullback_inv_snd]
    have hr : r ∈ F.s ⁻¹ᵁ V := by
      change F.s r ∈ V
      rw [hrs]
      exact hy
    rw [hV] at hr
    change F.t r ∈ V at hr
    rw [hrt] at hr
    exact hr
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- A quotient whose object scheme is covered by invariant affine opens with affine chart
quotients has an affine quotient map. -/
theorem isAffineHom_q_of_invariantOpenCover {K : Type*} (V : K → F.U.Opens)
    (hV : iSup V = ⊤) (hinv : ∀ k, F.IsInvariantOpen (V k)) (haff : ∀ k, IsAffineOpen (V k))
    (hq : ∀ k, (F.chart (V k).ι).HasAffineQuotient) : IsAffineHom Q.q := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro y
  obtain ⟨x, rfl⟩ := Q.q.surjective y
  have hx : x ∈ iSup V := by
    rw [hV]
    trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let W : Q.M.Opens := ⟨Q.q '' (V k : Set F.U), Q.q.isOpenMap _ (V k).2⟩
  have hW : Q.q ⁻¹ᵁ W = V k := by
    ext1
    exact Q.preimage_image_eq (hinv k)
  refine ⟨W, ⟨x, hk, rfl⟩, ?_, ?_⟩
  · apply Q.isAffineOpen_of_hasAffineQuotient_chart
    rw [hW]
    exact hq k
  · rw [hW]
    exact haff k

/-- The quotient of a relation with compact object scheme is compact. -/
lemma compactSpace [CompactSpace F.U] : CompactSpace Q.M :=
  Function.Surjective.compactSpace Q.q.continuous Q.q.surjective

/-- The quotient is locally of finite type over `Spec ℤ` when the object scheme is. -/
lemma locallyOfFiniteType_terminal [LocallyOfFiniteType (terminal.from F.U)] :
    LocallyOfFiniteType (terminal.from Q.M) := by
  apply locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp _ _ _ Q.q _
    inferInstance inferInstance inferInstance
  rw [terminal.comp_from]
  infer_instance

/-- The quotient by an affine quotient map of a quasi-separated object scheme is
quasi-separated. -/
lemma quasiSeparatedSpace [IsAffineHom Q.q] [QuasiSeparatedSpace F.U] :
    QuasiSeparatedSpace Q.M := by
  rw [quasiSeparatedSpace_iff_forall_affineOpens]
  intro U V
  have hU := U.2.preimage Q.q
  have hV := V.2.preimage Q.q
  have hc : IsCompact ((Q.q ⁻¹ᵁ (U : Q.M.Opens) : Set F.U) ∩ (Q.q ⁻¹ᵁ (V : Q.M.Opens))) :=
    QuasiSeparatedSpace.inter_isCompact _ _ (Q.q ⁻¹ᵁ _).2 hU.isCompact (Q.q ⁻¹ᵁ _).2
      hV.isCompact
  have := hc.image Q.q.continuous
  rwa [Scheme.Hom.coe_preimage, Scheme.Hom.coe_preimage, ← Set.preimage_inter,
    Set.image_preimage_eq _ Q.q.surjective] at this

end Basic

section Map

variable {E' E : EtaleEquivalenceRelation.{u}} {f : E'.U ⟶ E.U} {g : E'.R ⟶ E.R}

lemma unit_comp (h : IsCartesianHom E' E f g) : E'.unit ≫ g = f ≫ E.unit := by
  apply E.hom_ext
  · rw [Category.assoc, h.1, unit_t_assoc, Category.assoc, unit_t, Category.comp_id]
  · rw [Category.assoc, h.2.w, unit_s_assoc, Category.assoc, unit_s, Category.comp_id]

lemma comp_q_w (h : IsCartesianHom E' E f g) (Q : E.SchemeQuotient) :
    E'.t ≫ f ≫ Q.q = E'.s ≫ f ≫ Q.q := by
  rw [← Category.assoc, ← h.1, Category.assoc, Q.w, ← Category.assoc, h.2.w, Category.assoc]

/-- The morphism of quotients induced by a cartesian morphism. -/
noncomputable def map (h : IsCartesianHom E' E f g) (Q' : E'.SchemeQuotient)
    (Q : E.SchemeQuotient) : Q'.M ⟶ Q.M :=
  Q'.desc (f ≫ Q.q) (comp_q_w h Q)

@[reassoc (attr := simp)]
lemma q_map (h : IsCartesianHom E' E f g) (Q' : E'.SchemeQuotient) (Q : E.SchemeQuotient) :
    Q'.q ≫ map h Q' Q = f ≫ Q.q :=
  Q'.fac _ _

/-- The square formed by a cartesian morphism, the quotient maps and the induced morphism of
quotients is cartesian. -/
theorem isPullback_map (h : IsCartesianHom E' E f g) (Q' : E'.SchemeQuotient)
    (Q : E.SchemeQuotient) : IsPullback f Q'.q Q.q (map h Q' Q) := by
  refine isPullback_of_exists_local (q_map h Q' Q).symm ?_ ?_
  · intro T l l' hf hq
    have hr't : Q'.isPullback.lift l l' hq ≫ E'.t = l := Q'.isPullback.lift_fst _ _ _
    have hr's : Q'.isPullback.lift l l' hq ≫ E'.s = l' := Q'.isPullback.lift_snd _ _ _
    have hrg : Q'.isPullback.lift l l' hq ≫ g = l' ≫ E'.unit ≫ g := by
      apply E.hom_ext
      · rw [Category.assoc, h.1, reassoc_of% hr't, Category.assoc, Category.assoc, h.1,
          unit_t_assoc, hf]
      · rw [Category.assoc, h.2.w, reassoc_of% hr's, Category.assoc, Category.assoc, h.2.w,
          unit_s_assoc]
    have hr : Q'.isPullback.lift l l' hq = l' ≫ E'.unit := by
      apply h.2.hom_ext
      · rw [hrg, Category.assoc]
      · rw [hr's, Category.assoc, unit_s, Category.comp_id]
    rw [← hr't, hr, Category.assoc, unit_t, Category.comp_id]
  · intro T a b hab
    have hc : (pullback.fst b Q'.q ≫ a) ≫ Q.q = (pullback.snd b Q'.q ≫ f) ≫ Q.q := by
      rw [Category.assoc, hab, ← Category.assoc, pullback.condition, Category.assoc, q_map,
        Category.assoc]
    have hrs : Q.isPullback.lift _ _ hc ≫ E.s = pullback.snd b Q'.q ≫ f :=
      Q.isPullback.lift_snd _ _ _
    obtain ⟨r', hr'g, hr's⟩ : ∃ r', r' ≫ g = Q.isPullback.lift _ _ hc ∧
        r' ≫ E'.s = pullback.snd b Q'.q :=
      ⟨_, h.2.lift_fst _ _ hrs, h.2.lift_snd _ _ hrs⟩
    have h1 := h.1
    refine ⟨pullback b Q'.q, pullback.fst b Q'.q, r' ≫ E'.t, inferInstance, ?_, ?_⟩
    · rw [Category.assoc, ← h1, reassoc_of% hr'g, Q.isPullback.lift_fst]
    · rw [Category.assoc, Q'.w, reassoc_of% hr's, ← pullback.condition]

lemma map_id (Q : E.SchemeQuotient) : map (isCartesianHom_id E) Q Q = 𝟙 Q.M :=
  Q.hom_ext (by simp)

lemma map_comp {E₁ E₂ E₃ : EtaleEquivalenceRelation.{u}} {f₁ : E₁.U ⟶ E₂.U} {g₁ : E₁.R ⟶ E₂.R}
    {f₂ : E₂.U ⟶ E₃.U} {g₂ : E₂.R ⟶ E₃.R} (h₁ : IsCartesianHom E₁ E₂ f₁ g₁)
    (h₂ : IsCartesianHom E₂ E₃ f₂ g₂) (Q₁ : E₁.SchemeQuotient) (Q₂ : E₂.SchemeQuotient)
    (Q₃ : E₃.SchemeQuotient) :
    map (h₁.comp h₂) Q₁ Q₃ = map h₁ Q₁ Q₂ ≫ map h₂ Q₂ Q₃ :=
  Q₁.hom_ext (by simp)

/-- A quotient map is the base change of the quotient map of the target of a cartesian
morphism, so it is affine when that one is. -/
lemma isAffineHom_q (h : IsCartesianHom E' E f g) (Q' : E'.SchemeQuotient)
    (Q : E.SchemeQuotient) [IsAffineHom Q.q] : IsAffineHom Q'.q :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_map h Q' Q) inferInstance

/-- Induced maps of quotients are affine when the object map and the target quotient map are
affine. -/
theorem isAffineHom_map (h : IsCartesianHom E' E f g) (Q' : E'.SchemeQuotient)
    (Q : E.SchemeQuotient) [IsAffineHom f] [IsAffineHom Q.q] : IsAffineHom (map h Q' Q) := by
  constructor
  intro V hV
  apply Q'.isAffineOpen_of_hasAffineQuotient_chart
  have hpre : Q'.q ⁻¹ᵁ (map h Q' Q ⁻¹ᵁ V) = f ⁻¹ᵁ (Q.q ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, q_map, Scheme.Hom.comp_preimage]
  rw [hpre]
  exact etaleEquivalenceRelationCartesianAffineQuotient _ _ _ _
    (h.isCartesianHom_invariantOpenMap (Q.q ⁻¹ᵁ V)) ((hV.preimage Q.q).preimage f)
    (hV.preimage Q.q) (Q.hasAffineQuotient_chart V hV)

/-- Pull a quotient back along a cartesian morphism with affine object map, when the quotient
map is affine: the inverse images of the affine opens of the quotient form an invariant cover
whose chart relations have affine quotients. -/
theorem nonempty_of_isCartesianHom (h : IsCartesianHom E' E f g) (Q : E.SchemeQuotient)
    [IsAffineHom f] [IsAffineHom Q.q] : Nonempty E'.SchemeQuotient := by
  refine E'.nonempty_schemeQuotient_of_invariantOpenCover
    (fun V : Q.M.affineOpens => f ⁻¹ᵁ (Q.q ⁻¹ᵁ (V : Q.M.Opens))) ?_
    (fun V => h.isInvariantOpen_preimage (Q.isInvariantOpen_preimage V))
    (fun V => etaleEquivalenceRelationCartesianAffineQuotient _ _ _ _
      (h.isCartesianHom_invariantOpenMap _) ((V.2.preimage Q.q).preimage f)
      (V.2.preimage Q.q) (Q.hasAffineQuotient_chart V V.2))
  rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top]
  simp

/-- The chosen quotient pulled back along a cartesian morphism with affine object map. -/
noncomputable def ofIsCartesianHom (h : IsCartesianHom E' E f g) (Q : E.SchemeQuotient)
    [IsAffineHom f] [IsAffineHom Q.q] : E'.SchemeQuotient :=
  (nonempty_of_isCartesianHom h Q).some

end Map

section Limit

variable {I : Type u} [Category.{u} I] (D : I ⥤ EtaleEquivalenceRelation.{u})
  (Q : ∀ i, (D.obj i).SchemeQuotient)

/-- The diagram of quotients of a diagram of étale equivalence relations with cartesian
morphisms. -/
@[simps]
noncomputable def quotientFunctor : I ⥤ Scheme.{u} where
  obj i := (Q i).M
  map a := map (D.map a).isCartesian (Q _) (Q _)
  map_id i := (Q i).hom_ext (by simp)
  map_comp a b := (Q _).hom_ext (by simp)

variable {D} (c : Cone D) (Qc : c.pt.SchemeQuotient)

/-- The cone of quotients over the diagram of quotients, given a quotient of the cone point. -/
@[simps]
noncomputable def quotientCone : Cone (quotientFunctor D Q) where
  pt := Qc.M
  π :=
    { app i := map (c.π.app i).isCartesian Qc (Q i)
      naturality i j a := by
        have hw : (c.π.app i).objMap ≫ (D.map a).objMap = (c.π.app j).objMap :=
          congrArg CartesianMorphism.objMap (c.w a)
        apply Qc.hom_ext
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, q_map,
          quotientFunctor_obj, quotientFunctor_map, q_map_assoc]
        rw [reassoc_of% hw] }

variable [IsCofiltered I] (hc : IsLimit (objectFunctor.mapCone c))
include hc

/-- Morphisms into the quotient of the cone point are determined by their composites with the
cone of quotients. -/
lemma quotientCone_hom_ext {T : Scheme.{u}} {x y : T ⟶ Qc.M}
    (h : ∀ i, x ≫ map (c.π.app i).isCartesian Qc (Q i) =
      y ≫ map (c.π.app i).isCartesian Qc (Q i)) : x = y := by
  let e : pullback (pullback.fst x Qc.q ≫ y) Qc.q ⟶ T :=
    pullback.fst (pullback.fst x Qc.q ≫ y) Qc.q ≫ pullback.fst x Qc.q
  let u : pullback (pullback.fst x Qc.q ≫ y) Qc.q ⟶ c.pt.U :=
    pullback.fst (pullback.fst x Qc.q ≫ y) Qc.q ≫ pullback.snd x Qc.q
  let v : pullback (pullback.fst x Qc.q ≫ y) Qc.q ⟶ c.pt.U :=
    pullback.snd (pullback.fst x Qc.q ≫ y) Qc.q
  have hu : u ≫ Qc.q = e ≫ x := by
    simp only [u, e, Category.assoc, pullback.condition]
  have hv : v ≫ Qc.q = e ≫ y := by
    simp only [v, e, Category.assoc, ← pullback.condition]
  have he : Epi e := by
    dsimp only [e]
    infer_instance
  clear_value e u v
  have hq : ∀ i, (u ≫ (c.π.app i).objMap) ≫ (Q i).q = (v ≫ (c.π.app i).objMap) ≫ (Q i).q := by
    intro i
    simp only [Category.assoc, ← q_map (c.π.app i).isCartesian Qc (Q i)]
    rw [reassoc_of% hu, reassoc_of% hv, h i]
  let r : ∀ i, pullback (pullback.fst x Qc.q ≫ y) Qc.q ⟶ (D.obj i).R := fun i =>
    (Q i).isPullback.lift _ _ (hq i)
  have hrt : ∀ i, r i ≫ (D.obj i).t = u ≫ (c.π.app i).objMap := fun i =>
    (Q i).isPullback.lift_fst _ _ _
  have hrs : ∀ i, r i ≫ (D.obj i).s = v ≫ (c.π.app i).objMap := fun i =>
    (Q i).isPullback.lift_snd _ _ _
  let R : Cone (D ⋙ relationFunctor) :=
    { pt := pullback (pullback.fst x Qc.q ≫ y) Qc.q
      π :=
        { app := r
          naturality i j a := by
            have hw : (c.π.app i).objMap ≫ (D.map a).objMap = (c.π.app j).objMap :=
              congrArg CartesianMorphism.objMap (c.w a)
            apply (D.obj j).hom_ext
            · simp only [Functor.const_obj_obj, Functor.comp_obj, relationFunctor_obj,
                Functor.const_obj_map, Functor.comp_map, relationFunctor_map,
                Category.id_comp, Category.assoc, hrt]
              rw [(D.map a).isCartesian.1, reassoc_of% (hrt i), hw]
            · simp only [Functor.const_obj_obj, Functor.comp_obj, relationFunctor_obj,
                Functor.const_obj_map, Functor.comp_map, relationFunctor_map,
                Category.id_comp, Category.assoc, (D.map a).isCartesian.2.w, hrs]
              rw [reassoc_of% hrs, hw] } }
  let ρ : pullback (pullback.fst x Qc.q ≫ y) Qc.q ⟶ c.pt.R :=
    (CartesianDiagram.isLimitRelation D c hc).lift R
  have hρ : ∀ i, ρ ≫ (c.π.app i).relMap = r i := (CartesianDiagram.isLimitRelation D c hc).fac R
  have hρt : ρ ≫ c.pt.t = u := by
    apply hc.hom_ext
    intro i
    simp only [Functor.mapCone_pt, objectFunctor_obj, Functor.mapCone_π_app, objectFunctor_map,
      Category.assoc]
    have hti : c.pt.t ≫ (c.π.app i).objMap = (c.π.app i).relMap ≫ (D.obj i).t :=
      ((c.π.app i).isCartesian.1).symm
    rw [hti, reassoc_of% (hρ i), hrt]
  have hρs : ρ ≫ c.pt.s = v := by
    apply hc.hom_ext
    intro i
    simp only [Functor.mapCone_pt, objectFunctor_obj, Functor.mapCone_π_app, objectFunctor_map,
      Category.assoc]
    have hsi : c.pt.s ≫ (c.π.app i).objMap = (c.π.app i).relMap ≫ (D.obj i).s :=
      ((c.π.app i).isCartesian.2.w).symm
    rw [hsi, reassoc_of% (hρ i), hrs]
  have : e ≫ x = e ≫ y := by
    rw [← hu, ← hv, ← hρt, ← hρs, Category.assoc, Category.assoc, Qc.w]
  exact (cancel_epi e).1 this

/-- The limit of the quotients of a cofiltered cartesian diagram, whose object schemes have
the cone point as limit, is the quotient of the cone point. -/
noncomputable def isLimitQuotientCone : IsLimit (quotientCone Q c Qc) := by
  refine IsLimit.ofExistsUnique fun S => ?_
  let j₀ : I := (IsCofiltered.nonempty (C := I)).some
  let e : pullback (S.π.app j₀) (Q j₀).q ⟶ S.pt := pullback.fst _ _
  let b₀ : pullback (S.π.app j₀) (Q j₀).q ⟶ (D.obj j₀).U := pullback.snd _ _
  have hb : ∀ k : Over j₀, b₀ ≫ (Q j₀).q =
      (e ≫ S.π.app k.left) ≫ map (D.map k.hom).isCartesian (Q k.left) (Q j₀) := by
    intro k
    have := S.w k.hom
    simp only [quotientFunctor_obj, quotientFunctor_map] at this
    rw [Category.assoc, this, ← pullback.condition]
  let b : ∀ k : Over j₀, pullback (S.π.app j₀) (Q j₀).q ⟶ (D.obj k.left).U := fun k =>
    (isPullback_map (D.map k.hom).isCartesian (Q k.left) (Q j₀)).lift _ _ (hb k)
  have hb₁ : ∀ k : Over j₀, b k ≫ (D.map k.hom).objMap = b₀ := fun k =>
    (isPullback_map (D.map k.hom).isCartesian (Q k.left) (Q j₀)).lift_fst _ _ _
  have hb₂ : ∀ k : Over j₀, b k ≫ (Q k.left).q = e ≫ S.π.app k.left := fun k =>
    (isPullback_map (D.map k.hom).isCartesian (Q k.left) (Q j₀)).lift_snd _ _ _
  let B : Cone ((Over.forget j₀ ⋙ D) ⋙ objectFunctor) :=
    { pt := pullback (S.π.app j₀) (Q j₀).q
      π :=
        { app := b
          naturality k k' a := by
            simp only [Functor.const_obj_obj, Functor.comp_obj, Over.forget_obj,
              objectFunctor_obj, Functor.const_obj_map, Functor.comp_map, Over.forget_map,
              objectFunctor_map, Category.id_comp]
            apply (isPullback_map (D.map k'.hom).isCartesian (Q k'.left) (Q j₀)).hom_ext
            · rw [hb₁, Category.assoc, ← comp_objMap, ← D.map_comp, Over.w, hb₁]
            · rw [hb₂, Category.assoc, ← q_map (D.map a.left).isCartesian (Q k.left) (Q k'.left),
                reassoc_of% (hb₂ k)]
              have := S.w a.left
              simp only [quotientFunctor_obj, quotientFunctor_map] at this
              rw [this] } }
  let β : pullback (S.π.app j₀) (Q j₀).q ⟶ c.pt.U :=
    (CartesianDiagram.isLimitObjectAbove D j₀ c hc).lift B
  have hβ : ∀ k : Over j₀, β ≫ (c.π.app k.left).objMap = b k :=
    (CartesianDiagram.isLimitObjectAbove D j₀ c hc).fac B
  have key : ∀ i, (β ≫ Qc.q) ≫ map (c.π.app i).isCartesian Qc (Q i) = e ≫ S.π.app i := by
    intro i
    let k := IsCofiltered.min i j₀
    let K : Over j₀ := Over.mk (IsCofiltered.minToRight i j₀)
    have hw : (c.π.app k).objMap ≫ (D.map (IsCofiltered.minToLeft i j₀)).objMap =
        (c.π.app i).objMap :=
      congrArg CartesianMorphism.objMap (c.w _)
    have hS := S.w (IsCofiltered.minToLeft i j₀)
    simp only [quotientFunctor_obj, quotientFunctor_map] at hS
    have hβK : β ≫ (c.π.app k).objMap = b K := hβ K
    have hb₂K : b K ≫ (Q k).q = e ≫ S.π.app k := hb₂ K
    rw [Category.assoc, q_map, ← hw, Category.assoc, ← q_map (D.map _).isCartesian (Q k) (Q i),
      reassoc_of% hβK, ← Category.assoc, hb₂K, Category.assoc]
    exact congrArg (e ≫ ·) hS
  have hcompat : ∀ {W : Scheme.{u}} (g₁ g₂ : W ⟶ pullback (S.π.app j₀) (Q j₀).q),
      g₁ ≫ e = g₂ ≫ e → g₁ ≫ β ≫ Qc.q = g₂ ≫ β ≫ Qc.q := by
    intro W g₁ g₂ hg
    apply quotientCone_hom_ext Q c Qc hc
    intro i
    have h1 := key i
    calc (g₁ ≫ β ≫ Qc.q) ≫ map _ Qc (Q i) = g₁ ≫ e ≫ S.π.app i := by
          rw [← h1]; simp only [Category.assoc]
      _ = g₂ ≫ e ≫ S.π.app i := by rw [reassoc_of% hg]
      _ = (g₂ ≫ β ≫ Qc.q) ≫ map _ Qc (Q i) := by
          rw [← h1]; simp only [Category.assoc]
  refine ⟨EffectiveEpi.desc e (β ≫ Qc.q) hcompat, fun i => ?_, fun m hm => ?_⟩
  · rw [← cancel_epi e, ← Category.assoc, EffectiveEpi.fac]
    exact key i
  · apply quotientCone_hom_ext Q c Qc hc
    intro i
    have h1 : m ≫ map (c.π.app i).isCartesian Qc (Q i) = S.π.app i := hm i
    rw [h1, ← cancel_epi e, ← Category.assoc e, EffectiveEpi.fac]
    exact (key i).symm

end Limit

end SchemeQuotient

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
