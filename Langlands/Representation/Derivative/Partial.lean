import Langlands.Representation.Whittaker.EntrywiseCharacter
import Langlands.Representation.Jacquet.Localization
import Langlands.Group.GL.Padic

/-! # The actual partial derivative on products of general linear groups -/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

universe uF uV uW uX

namespace Partial

open GeneralLinear
open Jacquet.Localization

variable {F : Type uF} [CommRing F]

/-- The upper unipotents in the actual second factor, including rank zero. -/
abbrev unipotent (F : Type uF) [CommRing F] (k m : ℕ) :
    Subgroup (GeneralLinear k F × GeneralLinear m F) :=
  (⊥ : Subgroup (GeneralLinear k F)).prod (upperUnipotent m F)

/-- The actual first-factor subgroup. -/
abbrev actingSubgroup (F : Type uF) [CommRing F] (k m : ℕ) :
    Subgroup (GeneralLinear k F × GeneralLinear m F) :=
  (⊤ : Subgroup (GeneralLinear k F)).prod (⊥ : Subgroup (GeneralLinear m F))

/-- Projection of the specified product subgroup to its second unipotent factor. -/
def second (F : Type uF) [CommRing F] (k m : ℕ) :
    unipotent F k m →* upperUnipotent m F where
  toFun u := ⟨u.val.2, u.property.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Include an actual upper unipotent as `(1,u)`. -/
def includeUnipotent (F : Type uF) [CommRing F] (k m : ℕ) :
    upperUnipotent m F →* unipotent F k m where
  toFun u := ⟨(1, u.val), ⟨Subgroup.one_mem _, u.property⟩⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

/-- Exactly the published all-ranks character, composed with second projection. -/
def character (ψ : AddChar F ℂ) (k m : ℕ) : unipotent F k m →* ℂˣ :=
  (Whittaker.entrywiseCharacter ψ m).comp (second F k m)

@[simp] theorem character_include (ψ : AddChar F ℂ) (k m : ℕ)
    (u : upperUnipotent m F) :
    character ψ k m (includeUnipotent F k m u) = Whittaker.entrywiseCharacter ψ m u := rfl

@[simp] theorem character_succ (ψ : AddChar F ℂ) (k r : ℕ)
    (u : unipotent F k (r + 1)) :
    (character ψ k (r + 1) u : ℂ) =
      ψ (∑ i : Fin r, u.val.2.val i.castSucc i.succ) := rfl

@[simp] theorem character_zero (ψ : AddChar F ℂ) (k : ℕ) :
    character ψ k 0 = 1 := rfl

/-- The actual first-factor inclusion in the product group. -/
def first (F : Type uF) [CommRing F] (k m : ℕ) :
    GeneralLinear k F →* (GeneralLinear k F × GeneralLinear m F) where
  toFun g := (g, 1)
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

/-- The same inclusion, with codomain the specified acting subgroup. -/
def firstToActing (F : Type uF) [CommRing F] (k m : ℕ) :
    GeneralLinear k F →* actingSubgroup F k m :=
  (first F k m).codRestrict _ (fun _ => ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩)

/-- The first factor commutes with every element of the second-factor unipotents. -/
theorem commute (k m : ℕ) (a : actingSubgroup F k m) (u : unipotent F k m) :
    Commute a.val u.val := by
  have ha : a.val.2 = 1 := a.property.2
  have hu : u.val.1 = 1 := u.property.1
  change a.val * u.val = u.val * a.val
  ext <;> simp [ha, hu]

/-- Conjugation by the first factor is literally the identity on the unipotents. -/
theorem conjugation_eq (k m : ℕ) (a : actingSubgroup F k m) (u : unipotent F k m) :
    a.val * u.val * a.val⁻¹ = u.val := by
  rw [(commute k m a u).eq, mul_inv_cancel_right]

theorem normalizes (F : Type uF) [CommRing F] (k m : ℕ) :
    actingSubgroup F k m ≤ Subgroup.normalizer (unipotent F k m) := by
  intro a ha
  apply Subgroup.mem_normalizer_iff.mpr
  intro u
  constructor
  · intro hu
    simpa only [conjugation_eq k m ⟨a, ha⟩ ⟨u, hu⟩] using hu
  · intro hu
    have hu' : a⁻¹ * (a * u * a⁻¹) * a = a * u * a⁻¹ :=
      conjugation_eq k m ⟨a⁻¹, (actingSubgroup F k m).inv_mem ha⟩ ⟨_, hu⟩
    have he : u = a * u * a⁻¹ := by
      simpa [mul_assoc] using hu'
    rw [he]
    exact hu

theorem conjugate_eq (F : Type uF) [CommRing F] (k m : ℕ)
    (a : actingSubgroup F k m) (u : unipotent F k m) :
    conjugate (unipotent F k m) (actingSubgroup F k m) (normalizes F k m) a u = u :=
  Subtype.ext (conjugation_eq k m a u)

theorem character_invariant (ψ : AddChar F ℂ) (k m : ℕ) :
    IsInvariant (unipotent F k m) (actingSubgroup F k m)
      (normalizes F k m) (character ψ k m) := by
  intro a u
  rw [conjugate_eq]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {X : Type uX} [AddCommGroup X] [Module ℂ X]

/-- The existing localization relation span for the specified product subgroup. -/
abbrev relations (ψ : AddChar F ℂ) (k m : ℕ)
    (ρ : Representation ℂ (GeneralLinear k F × GeneralLinear m F) V) :=
  Jacquet.Localization.relations ρ (unipotent F k m) (character ψ k m)

/-- The actual quotient, still in the original carrier universe. -/
abbrev Quotient (ψ : AddChar F ℂ) (k m : ℕ)
    (ρ : Representation ℂ (GeneralLinear k F × GeneralLinear m F) V) :=
  Jacquet.Localization.Coinvariants ρ (unipotent F k m) (character ψ k m)

/-- The canonical linear quotient map. -/
abbrev mk (ψ : AddChar F ℂ) (k m : ℕ)
    (ρ : Representation ℂ (GeneralLinear k F × GeneralLinear m F) V) :
    V →ₗ[ℂ] Quotient ψ k m ρ :=
  Jacquet.Localization.mk ρ (unipotent F k m) (character ψ k m)

theorem mk_surjective (ψ : AddChar F ℂ) (k m : ℕ)
    (ρ : Representation ℂ (GeneralLinear k F × GeneralLinear m F) V) :
    Function.Surjective (mk ψ k m ρ) :=
  Jacquet.Localization.mk_surjective ρ _ _

/-- The generator is exactly the required `(1,u)` relation. -/
theorem generator_mem (ψ : AddChar F ℂ) (k m : ℕ)
    (ρ : Representation ℂ (GeneralLinear k F × GeneralLinear m F) V)
    (u : upperUnipotent m F) (v : V) :
    ρ (1, u.val) v - (Whittaker.entrywiseCharacter ψ m u : ℂ) • v ∈
      relations ψ k m ρ :=
  sub_mem_relations ρ _ _ (includeUnipotent F k m u) v

/-- The quotient uses exactly the span indexed by the actual second-factor unipotents. -/
theorem relations_eq_span (ψ : AddChar F ℂ) (k m : ℕ)
    (ρ : Representation ℂ (GeneralLinear k F × GeneralLinear m F) V) :
    relations ψ k m ρ =
      Submodule.span ℂ (Set.range fun uv : upperUnipotent m F × V =>
        ρ (1, uv.1.val) uv.2 - (Whittaker.entrywiseCharacter ψ m uv.1 : ℂ) • uv.2) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, v⟩, rfl⟩
    have hu : u.val = (1, (second F k m u).val) := Prod.ext u.property.1 rfl
    change ρ u.val v - (character ψ k m u : ℂ) • v ∈ _
    rw [hu]
    exact Submodule.subset_span (Set.mem_range_self (second F k m u, v))
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, v⟩, rfl⟩
    exact generator_mem ψ k m ρ u v

@[simp] theorem mk_eq_zero (ψ : AddChar F ℂ) (k m : ℕ)
    (ρ : Representation ℂ (GeneralLinear k F × GeneralLinear m F) V) (v : V) :
    mk ψ k m ρ v = 0 ↔ v ∈ relations ψ k m ρ :=
  Jacquet.Localization.mk_eq_zero ρ _ _ v

@[simp] theorem mk_unipotent (ψ : AddChar F ℂ) (k m : ℕ)
    (ρ : Representation ℂ (GeneralLinear k F × GeneralLinear m F) V)
    (u : upperUnipotent m F) (v : V) :
    mk ψ k m ρ (ρ (1, u.val) v) =
      (Whittaker.entrywiseCharacter ψ m u : ℂ) • mk ψ k m ρ v :=
  mk_apply_subgroup ρ _ _ (includeUnipotent F k m u) v

/-- Descend to the actual acting subgroup, then pull back along `g ↦ (g,1)`. -/
def action (ψ : AddChar F ℂ) (k m : ℕ)
    (ρ : Representation ℂ (GeneralLinear k F × GeneralLinear m F) V) :
    Representation ℂ (GeneralLinear k F) (Quotient ψ k m ρ) :=
  (Jacquet.Localization.action ρ (unipotent F k m) (character ψ k m)
    (actingSubgroup F k m) (normalizes F k m) (character_invariant ψ k m)).comp
      (firstToActing F k m)

@[simp] theorem action_mk (ψ : AddChar F ℂ) (k m : ℕ)
    (ρ : Representation ℂ (GeneralLinear k F × GeneralLinear m F) V)
    (g : GeneralLinear k F) (v : V) :
    action ψ k m ρ g (mk ψ k m ρ v) = mk ψ k m ρ (ρ (g, 1) v) := rfl

/-- The quotient map intertwines restriction to the first factor and the descended action. -/
def quotientMap (ψ : AddChar F ℂ) (k m : ℕ)
    (ρ : Representation ℂ (GeneralLinear k F × GeneralLinear m F) V) :
    Representation.IntertwiningMap (ρ.comp (first F k m)) (action ψ k m ρ) where
  toLinearMap := mk ψ k m ρ
  isIntertwining' _ := rfl

/-- The induced map on actual quotient classes. -/
def map (ψ : AddChar F ℂ) (k m : ℕ)
    {ρ : Representation ℂ (GeneralLinear k F × GeneralLinear m F) V}
    {σ : Representation ℂ (GeneralLinear k F × GeneralLinear m F) W}
    (f : ρ.IntertwiningMap σ) :
    (action ψ k m ρ).IntertwiningMap (action ψ k m σ) where
  toLinearMap := Jacquet.Localization.mapLinear (unipotent F k m) (character ψ k m) f
  isIntertwining' g :=
    (Jacquet.Localization.map (unipotent F k m) (character ψ k m)
      (actingSubgroup F k m) (normalizes F k m) (character_invariant ψ k m) f).isIntertwining'
        (firstToActing F k m g)

@[simp] theorem map_mk (ψ : AddChar F ℂ) (k m : ℕ)
    {ρ : Representation ℂ (GeneralLinear k F × GeneralLinear m F) V}
    {σ : Representation ℂ (GeneralLinear k F × GeneralLinear m F) W}
    (f : ρ.IntertwiningMap σ) (v : V) :
    map ψ k m f (mk ψ k m ρ v) = mk ψ k m σ (f v) := rfl

@[simp] theorem map_id (ψ : AddChar F ℂ) (k m : ℕ)
    (ρ : Representation ℂ (GeneralLinear k F × GeneralLinear m F) V) :
    map ψ k m (Representation.IntertwiningMap.id ρ) =
      Representation.IntertwiningMap.id (action ψ k m ρ) := by
  apply Representation.IntertwiningMap.ext
  exact Jacquet.Localization.hom_ext rfl

@[simp] theorem map_comp (ψ : AddChar F ℂ) (k m : ℕ)
    {ρ : Representation ℂ (GeneralLinear k F × GeneralLinear m F) V}
    {σ : Representation ℂ (GeneralLinear k F × GeneralLinear m F) W}
    {τ : Representation ℂ (GeneralLinear k F × GeneralLinear m F) X}
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
    map ψ k m (g.comp f) = (map ψ k m g).comp (map ψ k m f) := by
  apply Representation.IntertwiningMap.ext
  exact Jacquet.Localization.hom_ext rfl

section Topology

variable [TopologicalSpace F]

theorem continuous_first (k m : ℕ) : Continuous (first F k m) :=
  continuous_id.prodMk continuous_const

theorem continuous_firstToActing (k m : ℕ) : Continuous (firstToActing F k m) :=
  (continuous_first k m).subtype_mk _

theorem isSmooth_action (ψ : AddChar F ℂ) (k m : ℕ)
    (ρ : Representation ℂ (GeneralLinear k F × GeneralLinear m F) V)
    (hρ : IsSmooth ρ) : IsSmooth (action ψ k m ρ) :=
  isSmooth_comp (firstToActing F k m) (continuous_firstToActing k m)
    (Jacquet.Localization.isSmooth_action ρ _ _ _ _ (character_invariant ψ k m) hρ)

/-- Bundle the actual quotient action, with smoothness proved by transfer. -/
abbrev smoothObject (ψ : AddChar F ℂ) (k m : ℕ)
    (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F × GeneralLinear m F)) :
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F) :=
  SmoothRep.of (action ψ k m A.representation) (isSmooth_action ψ k m _ A.isSmooth)

/-- The partial-localization functor for the actual product topology. -/
def smoothFunctor (ψ : AddChar F ℂ) (k m : ℕ) :
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F × GeneralLinear m F) ⥤
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F) where
  obj := smoothObject ψ k m
  map f := SmoothRep.ofHom (map ψ k m (SmoothRep.hom f))
  map_id A := by
    change SmoothRep.ofHom (A := smoothObject ψ k m A) (B := smoothObject ψ k m A)
        (map ψ k m (Representation.IntertwiningMap.id _)) =
      SmoothRep.ofHom (Representation.IntertwiningMap.id _)
    rw [map_id]
  map_comp {A B C} f g := by
    change SmoothRep.ofHom (A := smoothObject ψ k m A) (B := smoothObject ψ k m C)
        (map ψ k m ((SmoothRep.hom g).comp (SmoothRep.hom f))) =
      SmoothRep.ofHom ((map ψ k m (SmoothRep.hom g)).comp (map ψ k m (SmoothRep.hom f)))
    rw [map_comp]

/-- First-factor restriction retains the entire original vector space. -/
def firstRestriction (k m : ℕ) :
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F × GeneralLinear m F) ⥤
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F) where
  obj A := SmoothRep.of (A.representation.comp (first F k m))
    (isSmooth_comp (first F k m) (continuous_first k m) A.isSmooth)
  map f := SmoothRep.ofHom
    { toLinearMap := (SmoothRep.hom f).toLinearMap
      isIntertwining' g := (SmoothRep.hom f).isIntertwining' (first F k m g) }
  map_id _ := rfl
  map_comp _ _ := rfl

end Topology

/-- In rank zero the specified unipotent subgroup is trivial. -/
theorem unipotent_zero_eq_one (k : ℕ) (u : unipotent F k 0) : u.val = 1 := by
  apply Prod.ext
  · exact u.property.1
  · exact Subsingleton.elim _ _

/-- Every relation vanishes when the second rank is zero. -/
theorem relations_zero (ψ : AddChar F ℂ) (k : ℕ)
    (ρ : Representation ℂ (GeneralLinear k F × GeneralLinear 0 F) V) :
    relations ψ k 0 ρ = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨u, v⟩, rfl⟩
  have hu := unipotent_zero_eq_one k u
  change ρ u.val v - (character ψ k 0 u : ℂ) • v ∈ (⊥ : Submodule ℂ V)
  simp [hu, character_zero]

/-- Rank-zero localization is equivariantly the original carrier with restricted action. -/
def zeroEquiv (ψ : AddChar F ℂ) (k : ℕ)
    (ρ : Representation ℂ (GeneralLinear k F × GeneralLinear 0 F) V) :
    (action ψ k 0 ρ).Equiv (ρ.comp (first F k 0)) where
  toLinearEquiv := (relations ψ k 0 ρ).quotEquivOfEqBot (relations_zero ψ k ρ)
  isIntertwining' g := by
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := mk_surjective ψ k 0 ρ q
    change (relations ψ k 0 ρ).quotEquivOfEqBot (relations_zero ψ k ρ)
        (mk ψ k 0 ρ (ρ (g, 1) v)) =
      ρ (g, 1) ((relations ψ k 0 ρ).quotEquivOfEqBot (relations_zero ψ k ρ) (mk ψ k 0 ρ v))
    rfl

@[simp] theorem zeroEquiv_mk (ψ : AddChar F ℂ) (k : ℕ)
    (ρ : Representation ℂ (GeneralLinear k F × GeneralLinear 0 F) V) (v : V) :
    zeroEquiv ψ k ρ (mk ψ k 0 ρ v) = v := rfl

section Topology

variable [TopologicalSpace F]

/-- The rank-zero equivalence is natural for every smooth intertwiner. -/
def zeroIso (ψ : AddChar F ℂ) (k : ℕ) :
    smoothFunctor.{uF,uV} ψ k 0 ≅ firstRestriction k 0 :=
  NatIso.ofComponents
    (fun A => SmoothRep.mkIso (zeroEquiv ψ k A.representation)) (by
      intro A B f
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply Jacquet.Localization.hom_ext
      ext v
      change zeroEquiv ψ k B.representation
          (mk ψ k 0 B.representation (SmoothRep.hom f v)) =
        SmoothRep.hom f (zeroEquiv ψ k A.representation (mk ψ k 0 A.representation v))
      simp only [zeroEquiv_mk])

end Topology
end Partial

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Zelevinsky's actual partial derivative, in every pair of natural ranks. -/
def partialDerivative (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) :
    letI := T.topology
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear m F.Carrier) ⥤
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier) := by
  letI := T.topology
  exact Partial.smoothFunctor ψ.complex k m

/-- Actual restriction to `g ↦ (g,1)` with the supplied field topology. -/
def productFirstRestriction (T : F.TopologicalData) (k m : ℕ) :
    letI := T.topology
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear m F.Carrier) ⥤
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier) := by
  letI := T.topology
  exact Partial.firstRestriction k m

/-- At second rank zero, the partial derivative naturally retains the original carrier. -/
def partialDerivativeZeroIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k : ℕ) :
    partialDerivative.{uF,uV} T ψ k 0 ≅ productFirstRestriction T k 0 := by
  letI := T.topology
  exact Partial.zeroIso ψ.complex k

/-- The actual quotient map into the object of the partial-derivative functor. -/
def partialDerivativeMk (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear m F.Carrier),
      A →ₗ[ℂ] (partialDerivative T ψ k m).obj A := by
  letI := T.topology
  intro A
  exact Partial.mk ψ.complex k m A.representation

theorem partialDerivativeMk_surjective (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear m F.Carrier),
      Function.Surjective (partialDerivativeMk T ψ k m A) := by
  let := T.topology
  intro A
  exact Partial.mk_surjective ψ.complex k m A.representation

theorem partialDerivativeMk_unipotent (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear m F.Carrier))
      (u : GeneralLinear.upperUnipotent m F.Carrier) (v : A),
      partialDerivativeMk T ψ k m A (A.representation (1, u.val) v) =
        (Whittaker.entrywiseCharacter ψ.complex m u : ℂ) • partialDerivativeMk T ψ k m A v := by
  let := T.topology
  intro A u v
  exact Partial.mk_unipotent ψ.complex k m A.representation u v

theorem partialDerivative_action_mk (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear m F.Carrier))
      (g : GeneralLinear k F.Carrier) (v : A),
      ((partialDerivative T ψ k m).obj A).representation g (partialDerivativeMk T ψ k m A v) =
        partialDerivativeMk T ψ k m A (A.representation (g, 1) v) := by
  intros
  rfl

theorem partialDerivative_map_mk (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear m F.Carrier)}
      (f : A ⟶ B) (v : A),
      SmoothRep.hom ((partialDerivative T ψ k m).map f) (partialDerivativeMk T ψ k m A v) =
        partialDerivativeMk T ψ k m B (SmoothRep.hom f v) := by
  intros
  rfl

theorem productFirstRestriction_obj_carrier (T : F.TopologicalData) (k m : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear m F.Carrier),
      ((productFirstRestriction T k m).obj A : Type uV) = A := by
  intros
  rfl

theorem partialDerivativeZeroIso_hom_mk (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear 0 F.Carrier))
      (v : A),
      SmoothRep.hom ((partialDerivativeZeroIso T ψ k).hom.app A)
        (partialDerivativeMk T ψ k 0 A v) = v := by
  intros
  rfl

theorem partialDerivativeZeroIso_inv_apply (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear 0 F.Carrier))
      (v : A),
      SmoothRep.hom ((partialDerivativeZeroIso T ψ k).inv.app A) v =
        partialDerivativeMk T ψ k 0 A v := by
  intros
  rfl

end Langlands.Derivative
