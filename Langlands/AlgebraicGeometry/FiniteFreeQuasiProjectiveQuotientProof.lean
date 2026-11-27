import Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement
import Langlands.AlgebraicGeometry.FiniteFreeQuasiAffineQuotientOver
import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.FunctionDescent
import Langlands.AlgebraicGeometry.Morphisms.FiniteFlatSourceDescent
import Langlands.AlgebraicGeometry.ProjectiveSpace.Structure
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType

/-! # Proof: quotients of quasi-projective schemes over a field by free finite group actions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry

/-- Two global sections that agree on every member of an open cover are equal. -/
theorem appTop_ext_of_openCover {T : Scheme.{u}} (𝒰 : T.OpenCover) {s s' : Γ(T, ⊤)}
    (h : ∀ i, (𝒰.f i).appTop s = (𝒰.f i).appTop s') : s = s' := by
  have he : (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).symm (fun _ => s) =
      (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).symm (fun _ => s') := by
    apply 𝒰.hom_ext
    intro i
    apply (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).injective
    funext k
    rw [AffineSpace.toSpecMvPolyIntEquiv_comp, AffineSpace.toSpecMvPolyIntEquiv_comp]
    simpa only [Equiv.apply_symm_apply] using h i
  simpa using
    congrFun ((AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).symm.injective he) PUnit.unit

namespace FiniteFreeSchemeAction

variable {G : Type u} [Group G] {X : Scheme.{u}} (A : FiniteFreeSchemeAction G X)

/-- The action as a homomorphism from the opposite group to the automorphism group: the
element `op g` acts by `act g`. The order of composition in `Aut X` is that of functions,
the opposite of the order in which `FiniteFreeSchemeAction` composes. -/
def autHom : Gᵐᵒᵖ →* Aut X where
  toFun g := Aut.of (A.act g.unop)
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    simp [A.one]
  map_mul' g h := by
    apply Aut.ext
    apply Iso.ext
    simp [A.mul]

@[simp] lemma autHom_asIso_hom (g : Gᵐᵒᵖ) : (A.autHom g).asIso.hom = (A.act g.unop).hom :=
  rfl

/-- An effective quotient exists as soon as every point has an affine open neighbourhood that
is invariant under the action. -/
theorem nonempty_effectiveQuotient_of_invariant_affine [Finite G] [X.IsSeparated]
    (h : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∀ g : G, (A.act g).hom ⁻¹ᵁ U = U) :
    Nonempty A.EffectiveQuotient := by
  let : IsFinite A.source := A.source_isFinite_of_finite
  let : IsFinite A.target := A.target_isFinite_of_finite
  have hj : ∀ {T : Scheme.{u}} (a b : T ⟶ A.relationScheme),
      a ≫ A.target = b ≫ A.target → a ≫ A.source = b ≫ A.source → a = b := by
    intro T a b ht hs
    apply (cancel_mono (prod.lift A.target A.source)).mp
    apply prod.hom_ext
    · simpa only [Category.assoc, prod.lift_fst] using ht
    · simpa only [Category.assoc, prod.lift_snd] using hs
  have he : ∀ T : Scheme.{u}, _root_.Equivalence
      (fun x y : T ⟶ X => ∃ r : T ⟶ A.relationScheme,
        r ≫ A.target = x ∧ r ≫ A.source = y) := by
    intro T
    refine ⟨A.reflexive T, ?_, ?_⟩
    · rintro x y ⟨r, hx, hy⟩
      obtain ⟨r', h1, h2⟩ := A.symmetric T r
      exact ⟨r', h1.trans hy, h2.trans hx⟩
    · rintro x y z ⟨r, hx, hy⟩ ⟨r', hy', hz⟩
      obtain ⟨r'', h1, h2⟩ := A.transitive T r r' (hy.trans hy'.symm)
      exact ⟨r'', h1.trans hx, h2.trans hz⟩
  have haff : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧
      ∀ r : A.relationScheme, A.target r = x → A.source r ∈ U := by
    intro x
    obtain ⟨U, hU, hx, hinv⟩ := h x
    refine ⟨U, hU, ?_⟩
    intro r hr
    obtain ⟨g, z, rfl⟩ := (sigmaOpenCover (fun _ : G => X)).exists_eq r
    change G at g
    change X at z
    change A.target ((Sigma.ι (fun _ : G => X) g) z) = x at hr
    change A.source ((Sigma.ι (fun _ : G => X) g) z) ∈ U
    have ht : A.target (Sigma.ι (fun _ : G => X) g z) = (A.act g).hom z :=
      congrArg (fun f : X ⟶ X => f z) (A.ι_target g)
    have hsource : A.source (Sigma.ι (fun _ : G => X) g z) = z :=
      congrArg (fun f : X ⟶ X => f z) (A.ι_source g)
    rw [hsource]
    have hz : z ∈ (A.act g).hom ⁻¹ᵁ U := by
      change (A.act g).hom z ∈ U
      rwa [← ht, hr]
    rwa [hinv g] at hz
  obtain ⟨Y, q, w, hfin, hflat, hlfp, hsurj, hpb, ⟨hc⟩⟩ :=
    Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation
      A.target A.source hj he haff
  let : IsFinite q := hfin
  let : Flat q := hflat
  let : Surjective q := hsurj
  have hq : Etale q := by
    apply MorphismProperty.of_isPullback_of_descendsAlong
      (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hpb
    · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
    · infer_instance
  exact ⟨⟨Y, q, w, hfin, hq, hsurj, hpb, hc⟩⟩

namespace EffectiveQuotient

variable {A} (Q : A.EffectiveQuotient)

/-- Two points with the same image in the quotient lie in one orbit. -/
theorem exists_act_eq_of_map_eq {x y : X} (h : Q.map x = Q.map y) :
    ∃ g : G, (A.act g).hom y = x := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y h
  obtain ⟨g, w, hw⟩ :=
    (sigmaOpenCover (fun _ : G => X)).exists_eq (Q.isPullback.isoPullback.inv z)
  change G at g
  change X at w
  change (Sigma.ι (fun _ : G => X) g) w = Q.isPullback.isoPullback.inv z at hw
  have ht : A.target (Q.isPullback.isoPullback.inv z) = x := by
    rw [← hz₁, ← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
  have hs : A.source (Q.isPullback.isoPullback.inv z) = y := by
    rw [← hz₂, ← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd]
  rw [← hw] at ht hs
  have ht' : A.target (Sigma.ι (fun _ : G => X) g w) = (A.act g).hom w :=
    congrArg (fun f : X ⟶ X => f w) (A.ι_target g)
  have hs' : A.source (Sigma.ι (fun _ : G => X) g w) = w :=
    congrArg (fun f : X ⟶ X => f w) (A.ι_source g)
  refine ⟨g, ?_⟩
  rw [← hs, hs', ← ht', ht]

/-- The image of an invariant open is open, and its preimage is the open itself. -/
theorem preimage_image_eq {U : X.Opens} (hU : ∀ g : G, (A.act g).hom ⁻¹ᵁ U = U) :
    Q.map ⁻¹ᵁ ⟨Q.map '' U, Q.map.isOpenMap _ U.isOpen⟩ = U := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨g, hg⟩ := Q.exists_act_eq_of_map_eq hxy
    have hx : x ∈ (A.act g).hom ⁻¹ᵁ U := by
      change (A.act g).hom x ∈ U
      rw [hg]
      exact hy
    rwa [hU g] at hx
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Invariant affine opens descend to affine opens of the quotient. -/
theorem exists_isAffineOpen_preimage_eq {U : X.Opens} (hU : IsAffineOpen U)
    (hinv : ∀ g : G, (A.act g).hom ⁻¹ᵁ U = U) :
    ∃ V : Q.scheme.Opens, IsAffineOpen V ∧ Q.map ⁻¹ᵁ V = U := by
  let V : Q.scheme.Opens := ⟨Q.map '' U, Q.map.isOpenMap _ U.isOpen⟩
  have hpre : Q.map ⁻¹ᵁ V = U := Q.preimage_image_eq hinv
  refine ⟨V, ?_, hpre⟩
  have : IsAffine (Q.map ⁻¹ᵁ V).toScheme := by
    change IsAffineOpen (Q.map ⁻¹ᵁ V)
    rw [hpre]
    exact hU
  let : Surjective (Q.map ∣_ V) :=
    IsZariskiLocalAtTarget.restrict (P := @Surjective) Q.surjective _
  exact FiniteLocallyFreeQuotient.isAffine_of_finite_flat_surjective (Q.map ∣_ V)

/-- An invariant section over an invariant open has equal pullbacks along two maps with equal
composite to the quotient, when both maps land in the open. -/
theorem appLE_top_eq_of_comp_map_eq {O : X.Opens} (hO : ∀ g : G, (A.act g).hom ⁻¹ᵁ O = O)
    (f : Γ(X, O)) (hf : ∀ g : G, (A.act g).hom.appLE O O (hO g).ge f = f)
    {T : Scheme.{u}} (a b : T ⟶ X) (hab : a ≫ Q.map = b ≫ Q.map)
    (ha : ⊤ ≤ a ⁻¹ᵁ O) (hb : ⊤ ≤ b ⁻¹ᵁ O) :
    a.appLE O ⊤ ha f = b.appLE O ⊤ hb f := by
  obtain ⟨𝒰, g, hg⟩ := (Q.eq_iff_locally_act a b).mp hab
  apply appTop_ext_of_openCover 𝒰
  intro i
  have hb' : ⊤ ≤ (𝒰.f i ≫ b) ⁻¹ᵁ O := fun x _ => hb (Set.mem_univ (𝒰.f i x))
  have hab' : 𝒰.f i ≫ a = (𝒰.f i ≫ b) ≫ (A.act (g i)).hom := by
    rw [hg i, Category.assoc]
  have hc : ⊤ ≤ ((𝒰.f i ≫ b) ≫ (A.act (g i)).hom) ⁻¹ᵁ O := by
    rw [← hab']
    exact fun x _ => ha (Set.mem_univ (𝒰.f i x))
  calc (𝒰.f i).appTop (a.appLE O ⊤ ha f)
      = (𝒰.f i ≫ a).appLE O ⊤ (hab' ▸ hc) f := by
        rw [Langlands.Scheme.UnitCocycleDescent.appTop_eq_appLE, ← CommRingCat.comp_apply,
          Scheme.Hom.appLE_comp_appLE]
    _ = ((𝒰.f i ≫ b) ≫ (A.act (g i)).hom).appLE O ⊤ hc f := by
        rw [Langlands.Scheme.UnitCocycleDescent.appLE_eq_of_eq hab' O ⊤ _ hc]
    _ = (𝒰.f i ≫ b).appLE O ⊤ hb' ((A.act (g i)).hom.appLE O O (hO (g i)).ge f) := by
        rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    _ = (𝒰.f i ≫ b).appLE O ⊤ hb' f := by rw [hf]
    _ = (𝒰.f i).appTop (b.appLE O ⊤ hb f) := by
        rw [Langlands.Scheme.UnitCocycleDescent.appTop_eq_appLE, ← CommRingCat.comp_apply,
          Scheme.Hom.appLE_comp_appLE]

/-- Invariant sections over an invariant open are pair invariant for the quotient map. -/
theorem isPairInvariant {O : X.Opens} (hO : ∀ g : G, (A.act g).hom ⁻¹ᵁ O = O)
    (f : Γ(X, O)) (hf : ∀ g : G, (A.act g).hom.appLE O O (hO g).ge f = f) :
    Langlands.Scheme.UnitCocycleDescent.IsPairInvariant Q.map O f := by
  intro T a b hab W ha hb
  apply Langlands.Scheme.UnitCocycleDescent.ι_appLE_injective W
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_comp_appLE]
  exact Q.appLE_top_eq_of_comp_map_eq hO f hf (W.ι ≫ a) (W.ι ≫ b)
    (by simp only [Category.assoc, hab]) _ _

/-- Pullback of sections along the quotient map is injective over every open. -/
theorem app_injective (V : Q.scheme.Opens) : Function.Injective (Q.map.app V) :=
  Langlands.Scheme.UnitCocycleDescent.app_injective Q.map V

/-- The sections of the quotient over an open are the invariant sections over its preimage. -/
theorem range_app_eq (V : Q.scheme.Opens) :
    Set.range (Q.map.app V) =
      {t | ∀ g : G, (A.act g).hom.appLE (Q.map ⁻¹ᵁ V) (Q.map ⁻¹ᵁ V)
        (by rw [← Scheme.Hom.comp_preimage, Q.invariant g]) t = t} := by
  ext t
  constructor
  · rintro ⟨s, rfl⟩ g
    rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      Langlands.Scheme.UnitCocycleDescent.appLE_eq_of_eq (Q.invariant g) V _ _ le_rfl]
  · intro ht
    have hO : ∀ g : G, (A.act g).hom ⁻¹ᵁ (Q.map ⁻¹ᵁ V) = Q.map ⁻¹ᵁ V := fun g => by
      rw [← Scheme.Hom.comp_preimage, Q.invariant g]
    exact Langlands.Scheme.UnitCocycleDescent.exists_app_eq_of_isPairInvariant Q.map V t
      (Q.isPairInvariant hO t ht)

end EffectiveQuotient

end FiniteFreeSchemeAction

open FiniteFreeSchemeAction in
/-- Free actions of finite groups on quasi-projective schemes over a field have
quasi-projective effective quotients. -/
theorem finiteFreeQuasiProjectiveQuotient : FiniteFreeQuasiProjectiveQuotientStatement := by
  intro K _ X s N j hj hjs G _ _ A hA
  have : IsImmersion j := hj
  -- `X` is quasi-compact: `j` is quasi-compact since projective space is locally Noetherian.
  have : IsLocallyNoetherian (ProjectiveSpace K N) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceToSpec K N)
  have : CompactSpace (ProjectiveSpace K N) :=
    QuasiCompact.compactSpace_of_compactSpace (projectiveSpaceToSpec K N)
  have : QuasiCompact j := by
    rw [← j.liftCoborder_ι]
    infer_instance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace j
  -- `X` is separated, being immersed in a separated scheme.
  have : X.IsSeparated := by
    constructor
    rw [← terminal.comp_from s, ← hjs]
    infer_instance
  have : Finite Gᵐᵒᵖ := Finite.of_equiv G MulOpposite.opEquiv
  -- An invariant affine open cover with an invariant cocycle of local equations.
  let ρ := A.autHom
  have hρ : ∀ γ : Gᵐᵒᵖ, (ρ γ).asIso.hom ≫ s = s := fun γ => hA γ.unop
  obtain ⟨r, U, hinv, w, hUaff, hcov, hw1, hw2, hw3, hw4⟩ :=
    Scheme.exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj
      K X s ⟨N, j, hj, hjs⟩ Gᵐᵒᵖ ρ hρ
  -- Every orbit lies in an invariant affine open, so the effective quotient exists.
  have horb : ∀ x : X, ∃ U' : X.Opens, IsAffineOpen U' ∧ x ∈ U' ∧
      ∀ g : G, (A.act g).hom ⁻¹ᵁ U' = U' := by
    intro x
    have hx : x ∈ (⨆ i, U i) := by
      rw [hcov]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨U i, hUaff i, hi, fun g => hinv (MulOpposite.op g) i⟩
  obtain ⟨Q⟩ := A.nonempty_effectiveQuotient_of_invariant_affine horb
  -- The descended structure morphism is locally of finite type.
  let t := Q.desc s hA
  have ht : Q.map ≫ t = s := Q.map_desc s hA
  have : LocallyOfFiniteType (Q.map ≫ t) := by
    rw [ht, ← hjs]
    infer_instance
  have : LocallyOfFiniteType t :=
    FiniteFlatSourceDescent.locallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective Q.map t
  -- The cover and its cocycle descend to the quotient.
  have hq : ∀ γ : Gᵐᵒᵖ, (ρ γ).asIso.hom ≫ Q.map = Q.map := fun γ => Q.invariant γ.unop
  have hrange : ∀ V : Q.scheme.Opens, Set.range (Q.map.app V) =
      {t | ∀ γ : Gᵐᵒᵖ, (ρ γ).asIso.hom.appLE (Q.map ⁻¹ᵁ V) (Q.map ⁻¹ᵁ V)
        (by rw [← Scheme.Hom.comp_preimage, hq γ]) t = t} := by
    intro V
    rw [Q.range_app_eq V]
    ext t
    exact ⟨fun h γ => h γ.unop, fun h g => h (MulOpposite.op g)⟩
  obtain ⟨V, v, hVaff, -, hVcov, hv1, hv2, hv3, -⟩ :=
    Scheme.exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant X Q.scheme Gᵐᵒᵖ ρ
      Q.map hq Q.map.surjective Q.app_injective hrange
      (fun U' hU' hinv' => Q.exists_isAffineOpen_preimage_eq hU'
        (fun g => hinv' (MulOpposite.op g)))
      r U hUaff hinv hcov w hw1 hw2 hw3 hw4
  -- The descended cocycle gives an immersion of the quotient into projective space.
  obtain ⟨M, j', hj', hj't⟩ :=
    Scheme.exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType
      K Q.scheme t r V hVaff hVcov v hv1 hv2 hv3
  exact ⟨Q, t, M, j', hj', hj't, ht⟩

end Langlands.AlgebraicGeometry
