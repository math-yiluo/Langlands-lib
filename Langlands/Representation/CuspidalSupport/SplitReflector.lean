import Langlands.Representation.Aubert.General.SupportCategoryExactnessReduction
import Langlands.Representation.Category.ExactFunctor
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Smooth.FiniteLengthGrothendieck
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Reflectors onto split properties of smooth representations -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.CuspidalSupport.SplitReflector

open SmoothRep Langlands.Aubert.General.ExactnessDetection

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A Boolean coproduct decomposition of `A` whose `true` summand satisfies `Q`
and whose `false` summand has no nonzero subquotient satisfying `Q`. -/
def HasSplitting (Q : ObjectProperty (SmoothRep.{0, uG, uV} ℂ G))
    (A : SmoothRep.{0, uG, uV} ℂ G) : Prop :=
  ∃ (Y : Bool → SmoothRep.{0, uG, uV} ℂ G) (j : ∀ b, Y b ⟶ A),
    Q (Y true) ∧
      (∀ D : SmoothRep.{0, uG, uV} ℂ G,
        Nontrivial D → SmoothRep.IsSubquotient D (Y false) → ¬ Q D) ∧
      Nonempty (IsColimit (Cofan.mk A j))

/-- A property closed under subrepresentations and quotients, along which every
object splits. -/
structure IsSplitSerre (Q : ObjectProperty (SmoothRep.{0, uG, uV} ℂ G)) : Prop where
  of_injective : ∀ {A B : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B),
    Function.Injective (hom f) → Q B → Q A
  of_surjective : ∀ {A B : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B),
    Function.Surjective (hom f) → Q A → Q B
  splitting : ∀ A, HasSplitting Q A

variable {Q : ObjectProperty (SmoothRep.{0, uG, uV} ℂ G)}

/-- A nonzero morphism moves some vector off zero. -/
theorem exists_hom_ne_zero {A B : SmoothRep.{0, uG, uV} ℂ G} {f : A ⟶ B} (hf : f ≠ 0) :
    ∃ v : A, hom f v ≠ 0 := by
  by_contra hn
  apply hf
  apply hom_ext'
  ext v
  by_contra hv
  exact hn ⟨v, hv⟩

/-- The image of a nonzero morphism is nontrivial. -/
theorem nontrivial_image {A B : SmoothRep.{0, uG, uV} ℂ G} {f : A ⟶ B} (hf : f ≠ 0) :
    Nontrivial (SmoothRep.image f) := by
  obtain ⟨v, hv⟩ := exists_hom_ne_zero hf
  exact ⟨⟨hom (imageProjection f) v, 0, fun heq => hv (congrArg Subtype.val heq)⟩⟩

/-- Every morphism from a `Q`-object to a remainder vanishes. -/
theorem eq_zero_of_to_remainder (hQ : IsSplitSerre Q) {R : SmoothRep.{0, uG, uV} ℂ G}
    (hR : ∀ D : SmoothRep.{0, uG, uV} ℂ G,
      Nontrivial D → SmoothRep.IsSubquotient D R → ¬ Q D)
    {X : SmoothRep.{0, uG, uV} ℂ G} (hX : Q X) (f : X ⟶ R) : f = 0 := by
  by_contra hf
  exact hR (SmoothRep.image f) (nontrivial_image hf)
    (subrepresentation_isSubrepresentation _).isSubquotient
    (hQ.of_surjective (imageProjection f) (imageProjection_surjective f) hX)

/-- Every morphism from a remainder to a `Q`-object vanishes. -/
theorem eq_zero_of_from_remainder (hQ : IsSplitSerre Q) {R : SmoothRep.{0, uG, uV} ℂ G}
    (hR : ∀ D : SmoothRep.{0, uG, uV} ℂ G,
      Nontrivial D → SmoothRep.IsSubquotient D R → ¬ Q D)
    {W : SmoothRep.{0, uG, uV} ℂ G} (hW : Q W) (f : R ⟶ W) : f = 0 := by
  by_contra hf
  exact hR (SmoothRep.image f) (nontrivial_image hf)
    (IsQuotient.isSubquotient ⟨imageProjection f, imageProjection_surjective f⟩)
    (hQ.of_injective (imageι f) (subtype_injective _ _) hW)

section Data

variable (hQ : IsSplitSerre Q) (A : SmoothRep.{0, uG, uV} ℂ G)

/-- The chosen summands of `A`. -/
def summand : Bool → SmoothRep.{0, uG, uV} ℂ G :=
  Classical.choose (hQ.splitting A)

/-- The chosen coproduct inclusions. -/
def inj : ∀ b, summand hQ A b ⟶ A :=
  Classical.choose (Classical.choose_spec (hQ.splitting A))

theorem summand_spec :
    Q (summand hQ A true) ∧
      (∀ D : SmoothRep.{0, uG, uV} ℂ G,
        Nontrivial D → SmoothRep.IsSubquotient D (summand hQ A false) → ¬ Q D) ∧
      Nonempty (IsColimit (Cofan.mk A (inj hQ A))) :=
  Classical.choose_spec (Classical.choose_spec (hQ.splitting A))

/-- The chosen coproduct is a colimit. -/
def isColimit : IsColimit (Cofan.mk A (inj hQ A)) :=
  (summand_spec hQ A).2.2.some

/-- The projection to the `Q`-summand. -/
def proj : A ⟶ summand hQ A true :=
  Cofan.IsColimit.desc (isColimit hQ A) (fun b => match b with
    | false => 0
    | true => 𝟙 _)

/-- The projection to the remainder. -/
def rem : A ⟶ summand hQ A false :=
  Cofan.IsColimit.desc (isColimit hQ A) (fun b => match b with
    | false => 𝟙 _
    | true => 0)

theorem inj_true_proj : inj hQ A true ≫ proj hQ A = 𝟙 _ :=
  Cofan.IsColimit.fac (isColimit hQ A) _ true

theorem inj_false_proj : inj hQ A false ≫ proj hQ A = 0 :=
  Cofan.IsColimit.fac (isColimit hQ A) _ false

theorem inj_true_rem : inj hQ A true ≫ rem hQ A = 0 :=
  Cofan.IsColimit.fac (isColimit hQ A) _ true

theorem inj_false_rem : inj hQ A false ≫ rem hQ A = 𝟙 _ :=
  Cofan.IsColimit.fac (isColimit hQ A) _ false

theorem proj_add_rem :
    proj hQ A ≫ inj hQ A true + rem hQ A ≫ inj hQ A false = 𝟙 A := by
  apply Cofan.IsColimit.hom_ext (isColimit hQ A)
  intro b
  change inj hQ A b ≫ _ = inj hQ A b ≫ 𝟙 A
  rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc]
  cases b
  · rw [inj_false_proj, inj_false_rem]
    simp
  · rw [inj_true_proj, inj_true_rem]
    simp

/-- Every morphism to a `Q`-object factors through the projection. -/
theorem proj_inj_comp {W : SmoothRep.{0, uG, uV} ℂ G} (hW : Q W) (φ : A ⟶ W) :
    proj hQ A ≫ inj hQ A true ≫ φ = φ := by
  apply Cofan.IsColimit.hom_ext (isColimit hQ A)
  intro b
  change inj hQ A b ≫ _ = inj hQ A b ≫ φ
  cases b
  · rw [← Category.assoc, inj_false_proj, zero_comp]
    exact (eq_zero_of_from_remainder hQ (summand_spec hQ A).2.1 hW _).symm
  · rw [← Category.assoc, inj_true_proj, Category.id_comp]

/-- The idempotent of `A` with image the `Q`-summand. -/
def idem : A ⟶ A := proj hQ A ≫ inj hQ A true

theorem idem_idem : idem hQ A ≫ idem hQ A = idem hQ A := by
  unfold idem
  rw [Category.assoc, ← Category.assoc (inj hQ A true), inj_true_proj, Category.id_comp]

variable {A} in
/-- Every morphism commutes with the idempotents. -/
theorem idem_comp {B : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B) :
    idem hQ A ≫ f = f ≫ idem hQ B := by
  unfold idem
  have h0 : inj hQ A true ≫ f ≫ rem hQ B = 0 :=
    eq_zero_of_to_remainder hQ (summand_spec hQ B).2.1 (summand_spec hQ A).1 _
  have h1 : inj hQ A true ≫ f = inj hQ A true ≫ f ≫ proj hQ B ≫ inj hQ B true := by
    conv_lhs => rw [← Category.comp_id f, ← proj_add_rem hQ B]
    rw [Preadditive.comp_add, Preadditive.comp_add]
    have h0' : inj hQ A true ≫ f ≫ rem hQ B ≫ inj hQ B false = 0 := by
      rw [← Category.assoc f, ← Category.assoc (inj hQ A true), h0, zero_comp]
    rw [h0', add_zero]
  have h2 := proj_inj_comp hQ A (summand_spec hQ B).1 (f ≫ proj hQ B)
  rw [Category.assoc, h1]
  have h3 := h2 =≫ inj hQ B true
  simp only [Category.assoc] at h3
  exact h3

end Data

section Adjunction

variable (hQ : IsSplitSerre Q)

/-- The left adjoint built from the chosen splittings. -/
def reflector : SmoothRep.{0, uG, uV} ℂ G ⥤ Q.FullSubcategory :=
  Adjunction.leftAdjointOfEquiv (G := Q.ι)
    (F_obj := fun A => ⟨summand hQ A true, (summand_spec hQ A).1⟩)
    (fun A W => {
      toFun := fun ψ => proj hQ A ≫ ψ.hom
      invFun := fun φ => ObjectProperty.homMk (inj hQ A true ≫ φ)
      left_inv := fun ψ => by
        apply ObjectProperty.hom_ext
        change inj hQ A true ≫ proj hQ A ≫ ψ.hom = ψ.hom
        rw [← Category.assoc, inj_true_proj, Category.id_comp]
      right_inv := fun φ => proj_inj_comp hQ A W.property φ })
    (fun A W W' g ψ => by
      change proj hQ A ≫ (ψ ≫ g).hom = (proj hQ A ≫ ψ.hom) ≫ g.hom
      rw [Category.assoc]
      rfl)

/-- The chosen left adjoint is a left adjoint. -/
def reflectorAdjunction : reflector hQ ⊣ Q.ι :=
  Adjunction.adjunctionOfEquivLeft _ _

include hQ in
theorem exists_leftAdjoint :
    ∃ sc : SmoothRep.{0, uG, uV} ℂ G ⥤ Q.FullSubcategory, Nonempty (sc ⊣ Q.ι) :=
  ⟨reflector hQ, ⟨reflectorAdjunction hQ⟩⟩

variable {sc : SmoothRep.{0, uG, uV} ℂ G ⥤ Q.FullSubcategory} (adj : sc ⊣ Q.ι)

include adj in
/-- Elementwise naturality of the unit. -/
theorem unit_naturality_apply {A B : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B) (a : A) :
    hom (sc.map f).hom (hom (adj.unit.app A) a) = hom (adj.unit.app B) (hom f a) := by
  have h := congrArg (fun t => hom t a) (adj.unit.naturality f)
  exact h.symm

include hQ in
/-- Every unit morphism is surjective. -/
theorem unit_surjective (A : SmoothRep.{0, uG, uV} ℂ G) :
    Function.Surjective (hom (adj.unit.app A)) := by
  let η := adj.unit.app A
  have hD : Q (SmoothRep.image η) :=
    hQ.of_injective (imageι η) (subtype_injective _ _) (sc.obj A).property
  let D : Q.FullSubcategory := ⟨SmoothRep.image η, hD⟩
  let ψ : sc.obj A ⟶ D := (adj.homEquiv A D).symm (imageProjection η)
  have hψ : η ≫ ψ.hom = imageProjection η := by
    have h := (adj.homEquiv A D).apply_symm_apply (imageProjection η)
    rw [adj.homEquiv_unit] at h
    exact h
  have hid : ψ ≫ (ObjectProperty.homMk (imageι η) : D ⟶ sc.obj A) = 𝟙 (sc.obj A) := by
    apply (adj.homEquiv A (sc.obj A)).injective
    rw [adj.homEquiv_unit, adj.homEquiv_unit, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_id]
    change η ≫ ψ.hom ≫ imageι η = η ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc, hψ]
    rfl
  intro y
  have hy := congrArg (fun t => hom t.hom y) hid
  change hom (imageι η) (hom ψ.hom y) = y at hy
  obtain ⟨a, ha⟩ := (hom ψ.hom y).2
  exact ⟨a, ha.trans hy⟩

include hQ in
/-- The unit vanishes exactly where the chosen projection vanishes. -/
theorem unit_apply_eq_zero_iff (A : SmoothRep.{0, uG, uV} ℂ G) (a : A) :
    hom (adj.unit.app A) a = 0 ↔ hom (proj hQ A) a = 0 := by
  constructor
  · intro ha
    let W : Q.FullSubcategory := ⟨summand hQ A true, (summand_spec hQ A).1⟩
    have h := (adj.homEquiv A W).apply_symm_apply (proj hQ A)
    rw [adj.homEquiv_unit] at h
    rw [← h]
    change hom ((adj.homEquiv A W).symm (proj hQ A)).hom (hom (adj.unit.app A) a) = 0
    rw [ha, map_zero]
  · intro ha
    rw [← proj_inj_comp hQ A (sc.obj A).property (adj.unit.app A)]
    change hom (inj hQ A true ≫ adj.unit.app A) (hom (proj hQ A) a) = 0
    rw [ha, map_zero]

theorem proj_apply_eq_zero_iff (A : SmoothRep.{0, uG, uV} ℂ G) (a : A) :
    hom (proj hQ A) a = 0 ↔ hom (idem hQ A) a = 0 := by
  constructor
  · intro ha
    change hom (inj hQ A true) (hom (proj hQ A) a) = 0
    rw [ha, map_zero]
  · intro ha
    have h := congrArg (fun t => hom t (hom (proj hQ A) a)) (inj_true_proj hQ A)
    change hom (proj hQ A) (hom (idem hQ A) a) = hom (proj hQ A) a at h
    rw [← h, ha, map_zero]

include hQ in
theorem unit_apply_eq_zero_iff_idem (A : SmoothRep.{0, uG, uV} ℂ G) (a : A) :
    hom (adj.unit.app A) a = 0 ↔ hom (idem hQ A) a = 0 :=
  (unit_apply_eq_zero_iff hQ adj A a).trans (proj_apply_eq_zero_iff hQ A a)

theorem idem_idem_apply (A : SmoothRep.{0, uG, uV} ℂ G) (a : A) :
    hom (idem hQ A) (hom (idem hQ A) a) = hom (idem hQ A) a :=
  congrArg (fun t => hom t a) (idem_idem hQ A)

theorem idem_comp_apply {A B : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B) (a : A) :
    hom f (hom (idem hQ A) a) = hom (idem hQ B) (hom f a) :=
  congrArg (fun t => hom t a) (idem_comp hQ f)

include hQ adj in
/-- Every left adjoint of the inclusion preserves actual short exact sequences. -/
theorem map_isShortExact {A B C : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B) (g : B ⟶ C)
    (hfg : IsShortExact (hom f) (hom g)) :
    IsShortExact (hom (sc.map f).hom) (hom (sc.map g).hom) := by
  obtain ⟨hf, hg, hex⟩ := hfg
  have hfgz : ∀ b, hom g b = 0 ↔ ∃ a, hom f a = b := fun b => by
    have h := SetLike.ext_iff.mp hex b
    simp only [LinearMap.mem_range, LinearMap.mem_ker] at h
    exact h.symm
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    obtain ⟨a, rfl⟩ := unit_surjective hQ adj A x
    obtain ⟨a', rfl⟩ := unit_surjective hQ adj A y
    rw [unit_naturality_apply adj, unit_naturality_apply adj] at hxy
    rw [← sub_eq_zero, ← map_sub] at hxy ⊢
    rw [← map_sub] at hxy
    rw [unit_apply_eq_zero_iff_idem hQ adj] at hxy ⊢
    apply hf
    rw [idem_comp_apply hQ f, hxy, map_zero]
  · intro y
    obtain ⟨c, rfl⟩ := unit_surjective hQ adj C y
    obtain ⟨b, rfl⟩ := hg c
    exact ⟨hom (adj.unit.app B) b, unit_naturality_apply adj g b⟩
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨a, rfl⟩ := unit_surjective hQ adj A x
      change hom (sc.map g).hom (hom (sc.map f).hom (hom (adj.unit.app A) a)) = 0
      rw [unit_naturality_apply adj, unit_naturality_apply adj,
        (hfgz (hom f a)).2 ⟨a, rfl⟩, map_zero]
    · intro y hy
      change hom (sc.map g).hom y = 0 at hy
      obtain ⟨b, rfl⟩ := unit_surjective hQ adj B y
      rw [unit_naturality_apply adj, unit_apply_eq_zero_iff_idem hQ adj,
        ← idem_comp_apply hQ g] at hy
      obtain ⟨a, ha⟩ := (hfgz _).1 hy
      refine ⟨hom (adj.unit.app A) a, ?_⟩
      change hom (sc.map f).hom (hom (adj.unit.app A) a) = hom (adj.unit.app B) b
      rw [unit_naturality_apply adj, ha, ← sub_eq_zero, ← map_sub,
        unit_apply_eq_zero_iff_idem hQ adj, map_sub, idem_idem_apply, sub_self]

/-- The unit at a `Q`-object is injective. -/
theorem unit_injective_of_mem {A : SmoothRep.{0, uG, uV} ℂ G} (hA : Q A) :
    Function.Injective (hom (adj.unit.app A)) := by
  let W : Q.FullSubcategory := ⟨A, hA⟩
  have h := (adj.homEquiv A W).apply_symm_apply (𝟙 A)
  rw [adj.homEquiv_unit] at h
  intro x y hxy
  have hx := congrArg (fun t => hom t x) h
  have hy := congrArg (fun t => hom t y) h
  change hom ((adj.homEquiv A W).symm (𝟙 A)).hom (hom (adj.unit.app A) x) = x at hx
  change hom ((adj.homEquiv A W).symm (𝟙 A)).hom (hom (adj.unit.app A) y) = y at hy
  rw [← hx, ← hy, hxy]

end Adjunction

end Langlands.CuspidalSupport.SplitReflector
