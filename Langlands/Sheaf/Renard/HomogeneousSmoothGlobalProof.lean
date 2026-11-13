import Langlands.Sheaf.Renard.HomogeneousSectionStatements

/-!
# Renard III.3.2: the smooth-global alpha–beta comparison

The published literal map `alphaSmoothGlobal` from the smooth part of the original
global sections to smooth induction of the identity-coset stalk is shown to be
bijective. Renard's beta is its inverse; the inverse laws, the displayed germ
formula and naturality follow from the published alpha laws.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.HomogeneousSmoothGlobalProof

open CategoryTheory Opposite TopologicalSpace
open Langlands.Induction
open Langlands.Sheaf.Equivariant
open Langlands.Sheaf.Renard.SectionActions
open Langlands.Sheaf.Renard.HomogeneousSections

section General

variable {G : Type} [Group G]
variable {X : Type} [TopologicalSpace X] [MulAction G X]

/-- Equal labels give equal stalk transports. -/
theorem stalkPull_congr (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{0} ℂ)
    [ContinuousConstSMul G X] {g g' : G} (e : g = g') (x y : X)
    (h : g • x = y) (h' : g' • x = y) :
    Godement.stalkPull F g x y h = Godement.stalkPull F g' x y h' := by
  subst e
  rfl

/-- The germ of a translated global section is the stalk transport of the original germ. -/
theorem germ_global_action [ContinuousConstSMul G X] (F : ActionSheaf G X) (k : G)
    (s : F.obj.obj (op ActionOpens.top)) (x y : X) (h : k⁻¹ • x = y) :
    (CompactSections.ordinary F.obj).Γgerm x (globalRepresentation F k s) =
      (Godement.stalkPull F.obj k⁻¹ x y h).hom
        ((CompactSections.ordinary F.obj).Γgerm y s) :=
  (congrArg (fun f => f.hom s)
    (Godement.germ_stalkPull_arrow F.obj (ActionOpens.sectionArrow k) x y h trivial)).symm

/-- Global sections of an action sheaf are determined by their original germs. -/
theorem global_ext (F : ActionSheaf G X) (s t : F.obj.obj (op ActionOpens.top))
    (h : ∀ x : X, (CompactSections.ordinary F.obj).Γgerm x s =
      (CompactSections.ordinary F.obj).Γgerm x t) : s = t :=
  TopCat.Presheaf.section_ext (underlying F) ⊤ s t (fun x _ => h x)

/-- A germ family that is locally given by sections is the family of germs of
one global section. -/
theorem exists_global_of_local (F : ActionSheaf G X)
    (v : ∀ x : X, (CompactSections.ordinary F.obj).stalk x)
    (hv : ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U)
      (t : (CompactSections.ordinary F.obj).obj (op U)),
        ∀ (y : X) (hy : y ∈ U), (CompactSections.ordinary F.obj).germ U y hy t = v y) :
    ∃ s : F.obj.obj (op ActionOpens.top),
      ∀ x : X, (CompactSections.ordinary F.obj).Γgerm x s = v x := by
  choose U hxU t ht using hv
  have hcompat : TopCat.Presheaf.IsCompatible (underlying F).1 U t := by
    intro i j
    apply TopCat.Presheaf.section_ext (underlying F)
    intro y hy
    change (CompactSections.ordinary F.obj).germ _ y hy
        ((CompactSections.ordinary F.obj).map (Opens.infLELeft (U i) (U j)).op (t i)) =
      (CompactSections.ordinary F.obj).germ _ y hy
        ((CompactSections.ordinary F.obj).map (Opens.infLERight (U i) (U j)).op (t j))
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, ht, ht]
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (underlying F) U ⊤
    (fun _ => homOfLE le_top)
    (fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩) t hcompat
  refine ⟨s, fun x => ?_⟩
  change (CompactSections.ordinary F.obj).germ ⊤ x trivial s = v x
  rw [← (CompactSections.ordinary F.obj).germ_res_apply (homOfLE le_top : U x ⟶ ⊤) x (hxU x) s]
  have := hs x
  change (CompactSections.ordinary F.obj).map (homOfLE le_top : U x ⟶ ⊤).op s = t x at this
  rw [this, ht]

end General

section Homogeneous

attribute [local instance] homogeneousAction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Every point of the homogeneous base is carried to the identity coset. -/
theorem exists_smul_eq_origin (x : LeftQuotient H) : ∃ a : G, a • x = origin H := by
  induction x using Quotient.inductionOn with
  | h k =>
    refine ⟨k, ?_⟩
    change quotientMap H (k * k⁻¹) = quotientMap H 1
    rw [mul_inv_cancel]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The stabilizer of the identity coset is contained in `H`. -/
theorem mem_of_smul_origin {h : G} (hh : h • origin H = origin H) : h ∈ H := by
  have e : Quotient.mk (QuotientGroup.rightRel H) (1 * h⁻¹) =
      Quotient.mk (QuotientGroup.rightRel H) 1 := hh
  have := QuotientGroup.rightRel_apply.mp (Quotient.exact e)
  simpa using this

variable (F : ActionSheaf G (LeftQuotient H))

/-- The germ of a global section at `y` is transported from the literal alpha value at any
group element carrying `y` to the identity coset. -/
theorem germ_eq_stalkPull_alpha (s : F.obj.obj (op ActionOpens.top)) (a : G)
    (y : LeftQuotient H) (h : a • y = origin H) :
    (CompactSections.ordinary F.obj).Γgerm y s =
      (Godement.stalkPull F.obj a y (origin H) h).hom (alphaFunction H F s a) := by
  have e := germ_global_action F a⁻¹ (globalRepresentation F a s) y (origin H)
    (by rw [inv_inv]; exact h)
  rw [Representation.inv_self_apply] at e
  rw [e, alphaFunction, stalkPull_congr F.obj (inv_inv a) y (origin H) _ h]

/-- Global sections with the same literal alpha function are equal. -/
theorem alphaFunction_injective (s t : F.obj.obj (op ActionOpens.top))
    (h : ∀ g : G, alphaFunction H F s g = alphaFunction H F t g) : s = t := by
  apply global_ext F
  intro y
  obtain ⟨a, ha⟩ := exists_smul_eq_origin H y
  rw [germ_eq_stalkPull_alpha H F s a y ha, germ_eq_stalkPull_alpha H F t a y ha, h a]

/-- Transport of the value at `a` to the stalk at a point that `a` carries to the origin. -/
def germAt (f : SmoothFunctions H (stalkRepresentation H F)) (a : G)
    (y : LeftQuotient H) (h : a • y = origin H) :
    (CompactSections.ordinary F.obj).stalk y :=
  (Godement.stalkPull F.obj a y (origin H) h).hom (eval H _ f a)

/-- The transported value does not depend on the chosen group element. -/
theorem germAt_eq (f : SmoothFunctions H (stalkRepresentation H F)) {a b : G}
    {y : LeftQuotient H} (ha : a • y = origin H) (hb : b • y = origin H) :
    germAt H F f a y ha = germAt H F f b y hb := by
  have hy : a⁻¹ • origin H = y := by rw [← ha, inv_smul_smul]
  have hmem : b * a⁻¹ ∈ H := mem_of_smul_origin H (by rw [mul_smul, hy, hb])
  let p : H := ⟨b * a⁻¹, hmem⟩
  have hcov : eval H _ f b = (Godement.stalkPull F.obj (p : G)⁻¹ (origin H) (origin H)
      (subgroup_fixes_origin H p⁻¹)).hom (eval H _ f a) := by
    have hc := f.1.2 p a
    have hpa : (p : G) * a = b := by simp [p]
    change f.1.1 ((p : G) * a) = _ at hc
    rw [hpa] at hc
    exact hc
  have hmul := Godement.stalkPull_mul F.obj b (p : G)⁻¹ y (origin H) (origin H) hb
    (subgroup_fixes_origin H p⁻¹)
  have hpt := congrArg (fun φ => φ.hom (eval H _ f a)) hmul
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hpt
  unfold germAt
  rw [hcov, ← hpt]
  exact congrArg (fun φ => φ.hom (eval H _ f a))
    (stalkPull_congr F.obj (show a = (b * a⁻¹)⁻¹ * b by group) y (origin H) ha _)

/-- A chosen germ family attached to a smooth induced function. -/
def germFamily (f : SmoothFunctions H (stalkRepresentation H F)) (y : LeftQuotient H) :
    (CompactSections.ordinary F.obj).stalk y :=
  germAt H F f (exists_smul_eq_origin H y).choose y (exists_smul_eq_origin H y).choose_spec

/-- The chosen germ family may be computed with any element carrying the point to the origin. -/
theorem germFamily_eq (f : SmoothFunctions H (stalkRepresentation H F)) {a : G}
    {y : LeftQuotient H} (h : a • y = origin H) :
    germFamily H F f y = germAt H F f a y h :=
  germAt_eq H F f _ h

/-- Near every point, the germ family is given by one global section. -/
theorem germFamily_local (hX : Langlands.Topology.IsLocallyProfinite (LeftQuotient H))
    (hF : IsSmoothAction F) (f : SmoothFunctions H (stalkRepresentation H F))
    (x : LeftQuotient H) :
    ∃ (U : Opens (LeftQuotient H)) (_ : x ∈ U) (σ : F.obj.obj (op ActionOpens.top)),
      ∀ (y : LeftQuotient H), y ∈ U →
        (CompactSections.ordinary F.obj).Γgerm y σ = germFamily H F f y := by
  obtain ⟨c, hc⟩ := Quotient.exists_rep x
  have hcx : quotientMap H c = x := hc
  obtain ⟨a, ha⟩ := exists_smul_eq_origin H x
  obtain ⟨σ, hσ⟩ := Langlands.Sheaf.CompactGerms.germ_surjective (underlying F) hX x
    (germFamily H F f x)
  obtain ⟨K', hK'⟩ := hF σ
  obtain ⟨K, hK⟩ := f.property
  let L : OpenSubgroup G := K ⊓ K'
  let U : Opens (LeftQuotient H) :=
    ⟨quotientMap H '' ((fun l => c * l) '' (L : Set G)),
      (Langlands.QuotientIntegration.leftQuotient_isOpenQuotientMap H).isOpenMap _
        (isOpenMap_mul_left c _ L.isOpen)⟩
  refine ⟨U, ⟨c, ⟨1, L.one_mem, mul_one c⟩, hcx⟩, σ.val, ?_⟩
  rintro y ⟨_, ⟨l, hl, rfl⟩, rfl⟩
  obtain ⟨m, hmL, rfl⟩ : ∃ m ∈ L, m⁻¹ = l := ⟨l⁻¹, L.inv_mem hl, inv_inv l⟩
  have hmL' := OpenSubgroup.mem_inf.mp hmL
  have hmy : m • x = quotientMap H (c * m⁻¹) := by rw [← hcx]; rfl
  have h1 : m⁻¹ • quotientMap H (c * m⁻¹) = x := by rw [← hmy, inv_smul_smul]
  have h2 : (a * m⁻¹) • quotientMap H (c * m⁻¹) = origin H := by rw [mul_smul, h1, ha]
  have hfix : globalRepresentation F m σ.val = σ.val :=
    congrArg Subtype.val (hK' ⟨m, hmL'.2⟩)
  have hfm : eval H _ f (a * m⁻¹) = eval H _ f a :=
    congrArg (fun φ : EquivariantFunctions H (stalkRepresentation H F) => φ.1 a)
      (hK ⟨m⁻¹, K.inv_mem hmL'.1⟩)
  have hσx : (CompactSections.ordinary F.obj).Γgerm x σ.val = germAt H F f a x ha := by
    rw [← germFamily_eq H F f ha]
    exact hσ
  rw [germFamily_eq H F f h2, ← hfix, germ_global_action F m σ.val _ x h1, hσx]
  unfold germAt
  rw [hfm]
  have hmul := Godement.stalkPull_mul F.obj m⁻¹ a (quotientMap H (c * m⁻¹)) x (origin H) h1 ha
  have hpt := congrArg (fun φ => φ.hom (eval H _ f a)) hmul
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hpt
  rw [← hpt]

/-- The germ family of a smooth induced function glues to a global section. -/
theorem exists_global_germFamily
    (hX : Langlands.Topology.IsLocallyProfinite (LeftQuotient H))
    (hF : IsSmoothAction F) (f : SmoothFunctions H (stalkRepresentation H F)) :
    ∃ s : F.obj.obj (op ActionOpens.top),
      ∀ y : LeftQuotient H, (CompactSections.ordinary F.obj).Γgerm y s = germFamily H F f y := by
  apply exists_global_of_local F (germFamily H F f)
  intro x
  obtain ⟨U, hxU, σ, hσ⟩ := germFamily_local H F hX hF f x
  refine ⟨U, hxU, (CompactSections.ordinary F.obj).map (homOfLE le_top : U ⟶ ⊤).op σ, ?_⟩
  intro y hy
  rw [TopCat.Presheaf.germ_res_apply]
  exact hσ y hy

/-- A global section with the germ family of `f` has literal alpha function `f`. -/
theorem alphaFunction_of_germs (f : SmoothFunctions H (stalkRepresentation H F))
    (s : F.obj.obj (op ActionOpens.top))
    (hs : ∀ y : LeftQuotient H,
      (CompactSections.ordinary F.obj).Γgerm y s = germFamily H F f y) (g : G) :
    alphaFunction H F s g = eval H _ f g := by
  have h1 : g • (g⁻¹ • origin H) = origin H := smul_inv_smul g (origin H)
  rw [alphaFunction, germ_global_action F g s (origin H) (g⁻¹ • origin H) rfl, hs,
    germFamily_eq H F f h1]
  unfold germAt
  have hmul := Godement.stalkPull_mul F.obj g⁻¹ g (origin H) (g⁻¹ • origin H) (origin H)
    rfl h1
  have hpt := congrArg (fun φ => φ.hom (eval H _ f g)) hmul
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hpt
  rw [← hpt, stalkPull_congr F.obj (mul_inv_cancel g) (origin H) (origin H) _ (one_smul G _),
    Godement.stalkPull_one]
  rfl

/-- The literal smooth-global alpha map is bijective. -/
theorem alphaSmoothGlobal_bijective
    (hX : Langlands.Topology.IsLocallyProfinite (LeftQuotient H))
    (F : SmoothActionSheaf G (LeftQuotient H)) :
    Function.Bijective (alphaSmoothGlobal H F.obj) := by
  constructor
  · intro s t hst
    apply Subtype.ext
    apply alphaFunction_injective H F.obj
    intro g
    exact congrArg (fun φ => eval H _ φ g) hst
  · intro f
    obtain ⟨s, hs⟩ := exists_global_germFamily H F.obj hX F.property f
    have hα := alphaFunction_of_germs H F.obj f s hs
    obtain ⟨K, hK⟩ := f.property
    have hsmooth : s ∈ Langlands.smoothVectors (globalRepresentation F.obj) := by
      refine ⟨K, ?_⟩
      change ∀ k : K, globalRepresentation F.obj (k : G) s = s
      intro k
      apply alphaFunction_injective H F.obj
      intro g
      rw [alphaFunction, ← global_mul, ← alphaFunction, hα, hα]
      exact congrArg (fun φ : EquivariantFunctions H _ => φ.1 g) (hK k)
    refine ⟨⟨s, hsmooth⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact hα g

/-- Renard's beta on smooth global sections: the inverse of the literal alpha map. -/
def beta (hX : Langlands.Topology.IsLocallyProfinite (LeftQuotient H))
    (F : SmoothActionSheaf G (LeftQuotient H)) :
    (smoothInduced H (stalkRepresentation H F.obj)).IntertwiningMap
      (Langlands.smoothPart (globalRepresentation F.obj)) :=
  ((alphaSmoothGlobal H F.obj).ofBijective
    (alphaSmoothGlobal_bijective H hX F)).symm.toIntertwiningMap

/-- Beta is a right inverse of the literal alpha map. -/
theorem alpha_beta (hX : Langlands.Topology.IsLocallyProfinite (LeftQuotient H))
    (F : SmoothActionSheaf G (LeftQuotient H))
    (f : SmoothFunctions H (stalkRepresentation H F.obj)) :
    alphaSmoothGlobal H F.obj (beta H hX F f) = f :=
  ((alphaSmoothGlobal H F.obj).ofBijective
    (alphaSmoothGlobal_bijective H hX F)).toLinearEquiv.apply_symm_apply f

/-- Beta is a left inverse of the literal alpha map. -/
theorem beta_alpha (hX : Langlands.Topology.IsLocallyProfinite (LeftQuotient H))
    (F : SmoothActionSheaf G (LeftQuotient H))
    (s : Langlands.smoothVectors (globalRepresentation F.obj)) :
    beta H hX F (alphaSmoothGlobal H F.obj s) = s :=
  ((alphaSmoothGlobal H F.obj).ofBijective
    (alphaSmoothGlobal_bijective H hX F)).toLinearEquiv.symm_apply_apply s

end Homogeneous

attribute [local instance] homogeneousAction

/-- Renard III.3.2 for smooth global sections. -/
theorem smoothGlobalAlphaBeta :
    HomogeneousSectionStatements.SmoothGlobalAlphaBetaStatement := by
  intro G _ _ _ _ hG H hH
  have hX := quotient_isLocallyProfinite H hG hH
  refine ⟨beta H hX, fun F => ⟨beta_alpha H hX F, alpha_beta H hX F, ?_⟩, ?_⟩
  · intro f g
    rw [germ_eq_stalkPull_alpha H F.obj (beta H hX F f).val g⁻¹ (g • origin H)
      (inv_smul_smul g (origin H))]
    rw [show alphaFunction H F.obj (beta H hX F f).val g⁻¹ =
        eval H (stalkRepresentation H F.obj) f g⁻¹ from
      congrArg (fun φ => eval H _ φ g⁻¹) (alpha_beta H hX F f)]
  · intro F F' u
    refine Representation.IntertwiningMap.ext (LinearMap.ext fun f => ?_)
    apply (alphaSmoothGlobal_bijective H hX F').1
    let T := smoothInducedMap H
      ((fixedStalkFunctor H (origin H) (subgroup_fixes_origin H)).map u.hom).hom
    have hn := congrArg (fun φ => φ (beta H hX F f)) (alphaSmoothGlobal_naturality H u.hom)
    have hr := alpha_beta H hX F' (T f)
    have hl := alpha_beta H hX F f
    exact hn.symm.trans ((congrArg T hl).trans hr.symm)

end Langlands.Sheaf.Renard.HomogeneousSmoothGlobalProof
