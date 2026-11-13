import Langlands.Sheaf.Renard.HomogeneousSectionStatements

/-!
# Renard III.3.2: the literal compact-section alpha is invertible

The forward map is the published `alphaCompact`. It is injective because a
section whose germs all vanish is zero. It is surjective because the displayed
original-stalk germs of an induced function glue to an actual compactly supported
global section. Beta is the inverse of the resulting bijection. The germ formula and
naturality follow from the inverse laws and the published forward naturality.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.HomogeneousCompactSectionProof

open CategoryTheory Opposite TopologicalSpace
open Langlands.Induction
open Langlands.Sheaf.Equivariant
open Langlands.Sheaf.Renard.SectionActions
open Langlands.Sheaf.Renard.HomogeneousSections
open Langlands.Sheaf.Renard.HomogeneousSectionStatements

section Gluing

variable {X : Type} [TopologicalSpace X]

/-- A locally represented family of original germs is the germ family of a global section. -/
theorem exists_global_of_locally_germ (F : TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of X))
    (σ : ∀ x : X, F.presheaf.stalk x)
    (hloc : ∀ x : X, ∃ (V : Opens (TopCat.of X)) (_ : x ∈ V) (u : F.presheaf.obj (op ⊤)),
      ∀ y (_ : y ∈ V), F.presheaf.Γgerm y u = σ y) :
    ∃ s : F.presheaf.obj (op ⊤), ∀ x, F.presheaf.Γgerm x s = σ x := by
  choose V hxV u hu using hloc
  let sf : ∀ x : X, F.presheaf.obj (op (V x)) := fun x =>
    F.presheaf.map (homOfLE le_top : V x ⟶ ⊤).op (u x)
  have hgerm : ∀ x y (hy : y ∈ V x), F.presheaf.germ (V x) y hy (sf x) = σ y := by
    intro x y hy
    rw [← hu x y hy]
    exact F.presheaf.Γgerm_res_apply y hy (u x)
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf V sf := by
    intro x y
    apply TopCat.Presheaf.section_ext F
    intro z hz
    refine (F.presheaf.germ_res_apply (Opens.infLELeft (V x) (V y)) z hz (sf x)).trans ?_
    refine Eq.trans ?_ (F.presheaf.germ_res_apply (Opens.infLERight (V x) (V y)) z hz (sf y)).symm
    exact (hgerm x z _).trans (hgerm y z _).symm
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' V ⊤ (fun x => homOfLE le_top)
    (fun x _ => Opens.mem_iSup.mpr ⟨x, hxV x⟩) sf hcompat
  refine ⟨s, fun x => ?_⟩
  rw [← F.presheaf.Γgerm_res_apply x (hxV x) s (i := homOfLE le_top), hs x, hgerm]

end Gluing

section StalkPull

variable {G : Type} [Group G] {X : Type} [TopologicalSpace X] [MulAction G X]
variable [ContinuousConstSMul G X]

/-- Composite stalk transports, in applied form, with an arbitrary product label. -/
theorem stalkPull_comp_apply (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{0} ℂ)
    (a b c : G) (x y z : X) (ha : a • x = y) (hb : b • y = z) (hc : c • x = z)
    (habc : b * a = c)
    (v : ((underlyingPresheaf G X (ModuleCat.{0} ℂ)).obj F).stalk z) :
    (Godement.stalkPull F a x y ha).hom ((Godement.stalkPull F b y z hb).hom v) =
      (Godement.stalkPull F c x z hc).hom v := by
  subst habc
  have hm := Godement.stalkPull_mul F a b x y z ha hb
  exact (congrArg (fun f => f.hom v) hm).symm

/-- Inverse labels cancel on the actual stalks. -/
theorem stalkPull_cancel (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{0} ℂ)
    (a b : G) (x y : X) (ha : a • x = y) (hb : b • y = x) (hab : b * a = 1)
    (v : ((underlyingPresheaf G X (ModuleCat.{0} ℂ)).obj F).stalk x) :
    (Godement.stalkPull F a x y ha).hom ((Godement.stalkPull F b y x hb).hom v) = v := by
  rw [stalkPull_comp_apply F a b 1 x y x ha hb (one_smul G x) hab, Godement.stalkPull_one]
  rfl

/-- Equal labels give equal stalk transports. -/
theorem stalkPull_label (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) {a b : G} (hab : a = b)
    (x y : X) (ha : a • x = y) :
    Godement.stalkPull F a x y ha = Godement.stalkPull F b x y (hab ▸ ha) := by
  subst hab
  rfl

/-- The germ of a translated global section is the stalk transport of the original germ. -/
theorem germ_global (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) (k : G) (x y : X)
    (h : k⁻¹ • x = y) (s : F.obj (op ActionOpens.top)) :
    (CompactSections.ordinary F).Γgerm x (CompactSections.globalRepresentation F k s) =
      (Godement.stalkPull F k⁻¹ x y h).hom ((CompactSections.ordinary F).Γgerm y s) :=
  (congrArg (fun f => f.hom s)
    (Godement.germ_stalkPull_arrow F (ActionOpens.sectionArrow k) x y h trivial)).symm

/-- The same germ formula, written with an inverse operator and a direct label. -/
theorem germ_global_inv (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) (k : G) (x y : X)
    (h : k • x = y) (s : F.obj (op ActionOpens.top)) :
    (CompactSections.ordinary F).Γgerm x (CompactSections.globalRepresentation F k⁻¹ s) =
      (Godement.stalkPull F k x y h).hom ((CompactSections.ordinary F).Γgerm y s) := by
  rw [germ_global F k⁻¹ x y (by rwa [inv_inv]) s, stalkPull_label F (inv_inv k)]

end StalkPull

section Homogeneous

attribute [local instance] homogeneousAction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- An element fixing the identity coset lies in the subgroup. -/
theorem mem_of_smul_origin (h : G) (hh : h • origin H = origin H) : h ∈ H := by
  have hq : quotientMap H (1 * h⁻¹) = quotientMap H 1 := hh
  have hr := QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
  simpa using hr

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Every group element carries its own coset to the identity coset. -/
theorem smul_self (a : G) : a • quotientMap H a = origin H := by
  change quotientMap H (a * a⁻¹) = quotientMap H 1
  rw [mul_inv_cancel]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The chosen representative of a coset carries it to the identity coset. -/
theorem out_smul (x : LeftQuotient H) : (Quotient.out x : G) • x = origin H := by
  have h := smul_self H (Quotient.out x)
  rwa [show quotientMap H (Quotient.out x) = x from Quotient.out_eq x] at h

variable (F : SmoothActionSheaf G (LeftQuotient H))

/-- Covariance of an induced function, with the coefficient action written as stalk transport. -/
theorem eval_covariant (f : CompactFunctions H (stalkRepresentation H F.obj)) (h : G)
    (hh : h ∈ H) (g : G) :
    eval H (stalkRepresentation H F.obj) f.val (h * g) =
      (Godement.stalkPull F.obj.obj h⁻¹ (origin H) (origin H)
        (subgroup_fixes_origin H ⟨h, hh⟩⁻¹)).hom
        (eval H (stalkRepresentation H F.obj) f.val g) :=
  f.val.val.property ⟨h, hh⟩ g

/-- The displayed original-stalk germ at a coset, computed from a chosen representative. -/
def betaGerm (f : CompactFunctions H (stalkRepresentation H F.obj)) (x : LeftQuotient H) :
    (CompactSections.ordinary F.obj.obj).stalk x :=
  (Godement.stalkPull F.obj.obj (Quotient.out x) x (origin H) (out_smul H x)).hom
    (eval H (stalkRepresentation H F.obj) f.val (Quotient.out x))

/-- The germ does not depend on the representative. -/
theorem betaGerm_eq (f : CompactFunctions H (stalkRepresentation H F.obj)) (g : G)
    (y : LeftQuotient H) (hy : g • y = origin H) :
    betaGerm H F f y = (Godement.stalkPull F.obj.obj g y (origin H) hy).hom
      (eval H (stalkRepresentation H F.obj) f.val g) := by
  have ha : (Quotient.out y : G) • y = origin H := out_smul H y
  have hy' : (Quotient.out y : G)⁻¹ • origin H = y := by rw [← ha, inv_smul_smul]
  have hmem : g * (Quotient.out y : G)⁻¹ ∈ H :=
    mem_of_smul_origin H _ (by rw [mul_smul, hy', hy])
  rw [show eval H (stalkRepresentation H F.obj) f.val g =
      eval H (stalkRepresentation H F.obj) f.val
        ((g * (Quotient.out y : G)⁻¹) * Quotient.out y) by rw [inv_mul_cancel_right],
    eval_covariant H F f _ hmem,
    stalkPull_comp_apply F.obj.obj g (g * (Quotient.out y : G)⁻¹)⁻¹ (Quotient.out y)
      y (origin H) (origin H) hy _ ha (by group)]
  rfl

/-- The literal compact alpha is injective: a section with all germs zero is zero. -/
theorem alphaCompact_injective : Function.Injective (alphaCompact H F) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  have hzero : ∀ g : G,
      (CompactSections.ordinary F.obj.obj).Γgerm (quotientMap H g) s.val = 0 := by
    intro g
    by_contra hne
    apply (alphaFunction_ne_zero_iff H F.obj s.val g).2 hne
    rw [← alphaCompact_apply H F s g, hs]
    rfl
  apply Subtype.ext
  apply TopCat.Presheaf.section_ext (underlying F.obj) ⊤
  intro x _
  have hx := hzero (Quotient.out x)
  rw [show quotientMap H (Quotient.out x) = x from Quotient.out_eq x] at hx
  exact hx.trans (map_zero _).symm

/-- The literal compact alpha is surjective: the displayed germs glue to a compact section. -/
theorem alphaCompact_surjective (hG : Langlands.Topology.IsLocallyProfinite G)
    (hH : IsClosed (H : Set G)) : Function.Surjective (alphaCompact H F) := by
  intro f
  have hX := quotient_isLocallyProfinite H hG hH
  have hloc : ∀ x : LeftQuotient H, ∃ (V : Opens (TopCat.of (LeftQuotient H))) (_ : x ∈ V)
      (u : (underlying F.obj).presheaf.obj (op ⊤)),
      ∀ y (_ : y ∈ V), (underlying F.obj).presheaf.Γgerm y u = betaGerm H F f y := by
    intro x
    obtain ⟨a, rfl⟩ : ∃ a : G, quotientMap H a = x := ⟨Quotient.out x, Quotient.out_eq x⟩
    obtain ⟨t, ht⟩ := Langlands.Sheaf.CompactGerms.germ_surjective (underlying F.obj) hX
      (origin H) (eval H (stalkRepresentation H F.obj) f.val a)
    let u0 := compactRepresentation F.obj a⁻¹ t
    obtain ⟨K, hK⟩ := F.property u0
    obtain ⟨K', hK'⟩ := f.val.property
    let L : OpenSubgroup G := K ⊓ K'
    refine ⟨⟨quotientMap H '' ((fun l => a * l) '' (L : Set G)),
      (Langlands.QuotientIntegration.leftQuotient_isOpenQuotientMap H).isOpenMap _
        (isOpenMap_mul_left a _ L.isOpen)⟩,
      ⟨a, ⟨1, L.one_mem, mul_one a⟩, rfl⟩, u0.val, ?_⟩
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    have hl' : l ∈ K ∧ l ∈ K' := OpenSubgroup.mem_inf.mp hl
    have hb : (a * l) • quotientMap H (a * l) = origin H := smul_self H (a * l)
    rw [betaGerm_eq H F f (a * l) _ hb]
    have hfl : eval H (stalkRepresentation H F.obj) f.val (a * l) =
        eval H (stalkRepresentation H F.obj) f.val a :=
      congrArg (fun φ : EquivariantFunctions H (stalkRepresentation H F.obj) => φ.1 a)
        ((Representation.mem_invariants _ _).mp hK' ⟨l, hl'.2⟩)
    have hul : u0.val = globalRepresentation F.obj (a * l)⁻¹ t.val := by
      have h1 := congrArg Subtype.val
        ((Representation.mem_invariants _ _).mp hK ⟨l⁻¹, inv_mem hl'.1⟩)
      change globalRepresentation F.obj l⁻¹ (globalRepresentation F.obj a⁻¹ t.val) =
        u0.val at h1
      rw [← h1, ← global_mul, mul_inv_rev]
    rw [hfl, hul, ← ht]
    exact germ_global_inv F.obj.obj (a * l) _ (origin H) hb t.val
  obtain ⟨s, hs⟩ := exists_global_of_locally_germ (underlying F.obj) (betaGerm H F f) hloc
  have halpha : ∀ g : G, alphaFunction H F.obj s g =
      eval H (stalkRepresentation H F.obj) f.val g := by
    intro g
    have hg : g • (g⁻¹ • origin H) = origin H := smul_inv_smul g (origin H)
    change (CompactSections.ordinary F.obj.obj).Γgerm (origin H)
      (CompactSections.globalRepresentation F.obj.obj g s) = _
    rw [germ_global F.obj.obj g (origin H) (g⁻¹ • origin H) rfl s]
    change (Godement.stalkPull F.obj.obj g⁻¹ (origin H) (g⁻¹ • origin H) rfl).hom
      ((underlying F.obj).presheaf.Γgerm (g⁻¹ • origin H) s) = _
    rw [hs, betaGerm_eq H F f g _ hg]
    exact stalkPull_cancel F.obj.obj g⁻¹ g (origin H) (g⁻¹ • origin H) rfl hg
      (mul_inv_cancel g) _
  have hcompact : s ∈ Langlands.Sheaf.CompactSupport.submodule
      (CompactSections.ordinary F.obj.obj) := by
    change IsCompact (Langlands.Sheaf.CompactSupport.support
      (CompactSections.ordinary F.obj.obj) s)
    rw [← quotientSupport_alphaFunction H F.obj s]
    have hfun : alphaFunction H F.obj s = eval H (stalkRepresentation H F.obj) f.val :=
      funext halpha
    rw [hfun]
    exact f.property
  refine ⟨⟨s, hcompact⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext g
  exact halpha g

/-- The constructed inverse: the inverse of the bijective literal compact alpha. -/
def beta (hG : Langlands.Topology.IsLocallyProfinite G) (hH : IsClosed (H : Set G)) :
    Representation.IntertwiningMap (compactInduced H (stalkRepresentation H F.obj))
      (compactRepresentation F.obj) :=
  let e := LinearEquiv.ofBijective (alphaCompact H F).toLinearMap
    ⟨alphaCompact_injective H F, alphaCompact_surjective H F hG hH⟩
  { toLinearMap := e.symm.toLinearMap
    isIntertwining' := e.isIntertwining_symm_isIntertwining (alphaCompact H F).isIntertwining' }

/-- Left inverse law: beta undoes the literal compact alpha. -/
theorem beta_alphaCompact (hG : Langlands.Topology.IsLocallyProfinite G)
    (hH : IsClosed (H : Set G)) (s) : beta H F hG hH (alphaCompact H F s) = s :=
  (LinearEquiv.ofBijective (alphaCompact H F).toLinearMap
    ⟨alphaCompact_injective H F, alphaCompact_surjective H F hG hH⟩).symm_apply_apply s

/-- Right inverse law: the literal compact alpha undoes beta. -/
theorem alphaCompact_beta (hG : Langlands.Topology.IsLocallyProfinite G)
    (hH : IsClosed (H : Set G)) (f) : alphaCompact H F (beta H F hG hH f) = f :=
  (LinearEquiv.ofBijective (alphaCompact H F).toLinearMap
    ⟨alphaCompact_injective H F, alphaCompact_surjective H F hG hH⟩).apply_symm_apply f

/-- The displayed original-stalk germ of beta at `g • o`. -/
theorem germ_beta (hG : Langlands.Topology.IsLocallyProfinite G) (hH : IsClosed (H : Set G))
    (f : CompactFunctions H (stalkRepresentation H F.obj)) (g : G) :
    (CompactSections.ordinary F.obj.obj).Γgerm (g • origin H) (beta H F hG hH f).val =
      (Godement.stalkPull F.obj.obj g⁻¹ (g • origin H) (origin H)
        (inv_smul_smul g (origin H))).hom
          (eval H (stalkRepresentation H F.obj) f.val g⁻¹) := by
  have hf : eval H (stalkRepresentation H F.obj) f.val g⁻¹ =
      alphaFunction H F.obj (beta H F hG hH f).val g⁻¹ := by
    rw [← alphaCompact_apply H F, alphaCompact_beta]
  rw [hf]
  change _ = (Godement.stalkPull F.obj.obj g⁻¹ (g • origin H) (origin H) _).hom
    ((CompactSections.ordinary F.obj.obj).Γgerm (origin H)
      (CompactSections.globalRepresentation F.obj.obj g⁻¹ (beta H F hG hH f).val))
  rw [germ_global_inv F.obj.obj g (origin H) (g • origin H) rfl]
  exact (stalkPull_cancel F.obj.obj g⁻¹ g (g • origin H) (origin H)
    (inv_smul_smul g (origin H)) rfl (mul_inv_cancel g) _).symm

end Homogeneous

attribute [local instance] homogeneousAction

/-- Renard III.3.2: the literal compact alpha has a natural equivariant inverse beta. -/
theorem compactAlphaBeta : CompactAlphaBetaStatement := by
  intro G _ _ _ _ hG H hH
  refine ⟨fun F => beta H F hG hH, fun F => ⟨beta_alphaCompact H F hG hH,
    alphaCompact_beta H F hG hH, germ_beta H F hG hH⟩, ?_⟩
  intro F F' u
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  apply alphaCompact_injective H F'
  change alphaCompact H F' (CompactSections.map u.hom (beta H F hG hH f)) =
    alphaCompact H F' (beta H F' hG hH (compactInducedMap H
      ((fixedStalkFunctor H (origin H) (subgroup_fixes_origin H)).map u.hom).hom f))
  rw [alphaCompact_beta]
  have hn := congrArg (fun φ => φ (beta H F hG hH f)) (alphaCompact_naturality H u)
  change compactInducedMap H _ (alphaCompact H F (beta H F hG hH f)) =
    alphaCompact H F' (CompactSections.map u.hom (beta H F hG hH f)) at hn
  rw [← hn, alphaCompact_beta]

end Langlands.Sheaf.Renard.HomogeneousCompactSectionProof
