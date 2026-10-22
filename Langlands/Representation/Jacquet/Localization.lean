import Langlands.Representation.Jacquet.SmoothTwist
import Langlands.Representation.Category.Basic

/-!
# Character-localized coinvariants

The quotient by the span of `ρ u v - (θ u : R) • v`, with its unnormalized
normalizing-subgroup action, functoriality, smoothness and trivial-character comparison.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Jacquet.Localization

universe uR uG uV uW uX

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G]
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [AddCommGroup X] [Module R X]

/-- The span of the exact character-localization relations. -/
def relations (ρ : Representation R G V) (U : Subgroup G) (θ : U →* Rˣ) :
    Submodule R V :=
  Submodule.span R (Set.range fun uv : U × V => ρ uv.1 uv.2 - (θ uv.1 : R) • uv.2)

/-- The actual quotient module, with its inherited module structure. -/
abbrev Coinvariants (ρ : Representation R G V) (U : Subgroup G) (θ : U →* Rˣ) :=
  V ⧸ relations ρ U θ

/-- The canonical linear quotient map. -/
abbrev mk (ρ : Representation R G V) (U : Subgroup G) (θ : U →* Rˣ) :
    V →ₗ[R] Coinvariants ρ U θ := (relations ρ U θ).mkQ

theorem sub_mem_relations (ρ : Representation R G V) (U : Subgroup G)
    (θ : U →* Rˣ) (u : U) (v : V) :
    ρ u v - (θ u : R) • v ∈ relations ρ U θ :=
  Submodule.subset_span (Set.mem_range_self (u, v))

theorem mk_surjective (ρ : Representation R G V) (U : Subgroup G) (θ : U →* Rˣ) :
    Function.Surjective (mk ρ U θ) := (relations ρ U θ).mkQ_surjective

@[simp] theorem mk_eq_zero (ρ : Representation R G V) (U : Subgroup G)
    (θ : U →* Rˣ) (v : V) : mk ρ U θ v = 0 ↔ v ∈ relations ρ U θ :=
  Submodule.Quotient.mk_eq_zero _

theorem mk_eq_iff (ρ : Representation R G V) (U : Subgroup G)
    (θ : U →* Rˣ) (v w : V) :
    mk ρ U θ v = mk ρ U θ w ↔ v - w ∈ relations ρ U θ :=
  Submodule.Quotient.eq _

theorem ker_mk (ρ : Representation R G V) (U : Subgroup G) (θ : U →* Rˣ) :
    LinearMap.ker (mk ρ U θ) = relations ρ U θ := by
  ext v
  exact mk_eq_zero ρ U θ v

@[simp] theorem mk_apply_subgroup (ρ : Representation R G V) (U : Subgroup G)
    (θ : U →* Rˣ) (u : U) (v : V) :
    mk ρ U θ (ρ u v) = (θ u : R) • mk ρ U θ v := by
  rw [← map_smul]
  exact (mk_eq_iff ρ U θ _ _).2 (sub_mem_relations ρ U θ u v)

/-- A linear map kills the relation span exactly when it kills every generator. -/
theorem relations_le_ker_iff (ρ : Representation R G V) (U : Subgroup G)
    (θ : U →* Rˣ) (f : V →ₗ[R] W) :
    relations ρ U θ ≤ LinearMap.ker f ↔
      ∀ (u : U) (v : V), f (ρ u v) = (θ u : R) • f v := by
  constructor
  · intro h u v
    have hv := h (sub_mem_relations ρ U θ u v)
    simpa only [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] using hv
  · intro h
    apply Submodule.span_le.2
    rintro _ ⟨⟨u, v⟩, rfl⟩
    change f (ρ u v - (θ u : R) • v) = 0
    simp only [map_sub, map_smul, sub_eq_zero, h]

/-- Factor a linear map killing the exact character relations through the quotient. -/
def lift (ρ : Representation R G V) (U : Subgroup G) (θ : U →* Rˣ)
    (f : V →ₗ[R] W) (hf : ∀ (u : U) (v : V), f (ρ u v) = (θ u : R) • f v) :
    Coinvariants ρ U θ →ₗ[R] W :=
  (relations ρ U θ).liftQ f ((relations_le_ker_iff ρ U θ f).2 hf)

@[simp] theorem lift_mk (ρ : Representation R G V) (U : Subgroup G) (θ : U →* Rˣ)
    (f : V →ₗ[R] W) (hf : ∀ (u : U) (v : V), f (ρ u v) = (θ u : R) • f v)
    (v : V) : lift ρ U θ f hf (mk ρ U θ v) = f v := rfl

@[ext] theorem hom_ext {ρ : Representation R G V} {U : Subgroup G} {θ : U →* Rˣ}
    {f g : Coinvariants ρ U θ →ₗ[R] W} (h : f ∘ₗ mk ρ U θ = g ∘ₗ mk ρ U θ) :
    f = g := Submodule.linearMap_qext _ h

theorem lift_unique (ρ : Representation R G V) (U : Subgroup G) (θ : U →* Rˣ)
    (f : V →ₗ[R] W) (hf : ∀ (u : U) (v : V), f (ρ u v) = (θ u : R) • f v)
    (g : Coinvariants ρ U θ →ₗ[R] W) (hg : g ∘ₗ mk ρ U θ = f) :
    g = lift ρ U θ f hf := hom_ext hg

/-- Existence and uniqueness formulation of the linear universal property. -/
theorem existsUnique_lift_iff (ρ : Representation R G V) (U : Subgroup G)
    (θ : U →* Rˣ) (f : V →ₗ[R] W) :
    (∃! g : Coinvariants ρ U θ →ₗ[R] W, g ∘ₗ mk ρ U θ = f) ↔
      ∀ (u : U) (v : V), f (ρ u v) = (θ u : R) • f v := by
  constructor
  · rintro ⟨g, hg, _⟩ u v
    rw [← hg]
    change g (mk ρ U θ (ρ u v)) = (θ u : R) • g (mk ρ U θ v)
    rw [mk_apply_subgroup, map_smul]
  · intro hf
    exact ⟨lift ρ U θ f hf, rfl, fun g hg => lift_unique ρ U θ f hf g hg⟩

/-- Conjugation into `U`, using the actual normalizer hypothesis. -/
def conjugate (U M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U) (m : M) (u : U) : U :=
  ⟨(m : G) * u * (m : G)⁻¹,
    ((Subgroup.mem_normalizer_iff.mp (hMU m.property)) u).mp u.property⟩

/-- The character is fixed by conjugation by every element of the acting subgroup. -/
def IsInvariant (U M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U) (θ : U →* Rˣ) : Prop :=
  ∀ (m : M) (u : U), θ (conjugate U M hMU m u) = θ u

/-- Applying `ρ m` to a generator gives the conjugate generator at `ρ m v`. -/
theorem relations_stable (ρ : Representation R G V) (U : Subgroup G) (θ : U →* Rˣ)
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U) (hθ : IsInvariant U M hMU θ) (m : M) :
    relations ρ U θ ≤ (relations ρ U θ).comap (ρ m) := by
  apply Submodule.span_le.2
  rintro _ ⟨⟨u, v⟩, rfl⟩
  change ρ m (ρ u v - (θ u : R) • v) ∈ relations ρ U θ
  have h := sub_mem_relations ρ U θ (conjugate U M hMU m u) (ρ m v)
  rw [hθ m u] at h
  simpa [conjugate] using h

/-- The relation submodule as an actual subrepresentation of the restricted action. -/
def relationsSubrepresentation (ρ : Representation R G V) (U : Subgroup G)
    (θ : U →* Rˣ) (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U)
    (hθ : IsInvariant U M hMU θ) : Subrepresentation (ρ.comp M.subtype) where
  toSubmodule := relations ρ U θ
  apply_mem_toSubmodule m := relations_stable ρ U θ M hMU hθ m

/-- The unnormalized action of the subgroup preserving `U` and its character. -/
def action (ρ : Representation R G V) (U : Subgroup G) (θ : U →* Rˣ)
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U) (hθ : IsInvariant U M hMU θ) :
    Representation R M (Coinvariants ρ U θ) :=
  Representation.quotient (ρ.comp M.subtype) (relations ρ U θ)
    (relations_stable ρ U θ M hMU hθ)

@[simp] theorem action_mk (ρ : Representation R G V) (U : Subgroup G) (θ : U →* Rˣ)
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U) (hθ : IsInvariant U M hMU θ)
    (m : M) (v : V) : action ρ U θ M hMU hθ m (mk ρ U θ v) = mk ρ U θ (ρ m v) := rfl

/-- The quotient map intertwines the restricted and descended actions. -/
def quotientMap (ρ : Representation R G V) (U : Subgroup G) (θ : U →* Rˣ)
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U) (hθ : IsInvariant U M hMU θ) :
    Representation.IntertwiningMap (ρ.comp M.subtype) (action ρ U θ M hMU hθ) where
  toLinearMap := mk ρ U θ
  isIntertwining' _ := rfl

/-- Every ambient intertwiner induces a linear map between localized quotients. -/
def mapLinear {ρ : Representation R G V} {σ : Representation R G W}
    (U : Subgroup G) (θ : U →* Rˣ) (f : ρ.IntertwiningMap σ) :
    Coinvariants ρ U θ →ₗ[R] Coinvariants σ U θ :=
  lift ρ U θ (mk σ U θ ∘ₗ f.toLinearMap) (fun u v => by
    change mk σ U θ (f (ρ u v)) = (θ u : R) • mk σ U θ (f v)
    rw [Representation.IntertwiningMap.isIntertwining ρ σ f u v, mk_apply_subgroup])

/-- The induced map is equivariant for the descended subgroup actions. -/
def map {ρ : Representation R G V} {σ : Representation R G W}
    (U : Subgroup G) (θ : U →* Rˣ) (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U)
    (hθ : IsInvariant U M hMU θ) (f : ρ.IntertwiningMap σ) :
    (action ρ U θ M hMU hθ).IntertwiningMap (action σ U θ M hMU hθ) where
  toLinearMap := mapLinear U θ f
  isIntertwining' m := by
    apply hom_ext
    ext v
    change mk σ U θ (f (ρ m v)) = mk σ U θ (σ m (f v))
    rw [Representation.IntertwiningMap.isIntertwining ρ σ f m v]

@[simp] theorem map_mk {ρ : Representation R G V} {σ : Representation R G W}
    (U : Subgroup G) (θ : U →* Rˣ) (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U)
    (hθ : IsInvariant U M hMU θ) (f : ρ.IntertwiningMap σ) (v : V) :
    map U θ M hMU hθ f (mk ρ U θ v) = mk σ U θ (f v) := rfl

theorem map_comp_quotientMap {ρ : Representation R G V} {σ : Representation R G W}
    (U : Subgroup G) (θ : U →* Rˣ) (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U)
    (hθ : IsInvariant U M hMU θ) (f : ρ.IntertwiningMap σ) :
    (map U θ M hMU hθ f).comp (quotientMap ρ U θ M hMU hθ) =
      (quotientMap σ U θ M hMU hθ).comp (Jacquet.restrictMap f M) := by
  ext v
  rfl

@[simp] theorem map_id (ρ : Representation R G V) (U : Subgroup G) (θ : U →* Rˣ)
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U) (hθ : IsInvariant U M hMU θ) :
    map U θ M hMU hθ (Representation.IntertwiningMap.id ρ) =
      Representation.IntertwiningMap.id (action ρ U θ M hMU hθ) := by
  apply Representation.IntertwiningMap.ext
  exact hom_ext rfl

@[simp] theorem map_comp {ρ : Representation R G V} {σ : Representation R G W}
    {τ : Representation R G X} (U : Subgroup G) (θ : U →* Rˣ) (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer U) (hθ : IsInvariant U M hMU θ)
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
    map U θ M hMU hθ (g.comp f) =
      (map U θ M hMU hθ g).comp (map U θ M hMU hθ f) := by
  apply Representation.IntertwiningMap.ext
  exact hom_ext rfl

/-- Localization as a functor on Mathlib's representation categories. -/
def functor (U : Subgroup G) (θ : U →* Rˣ) (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer U) (hθ : IsInvariant U M hMU θ) :
    Rep.{uV} R G ⥤ Rep.{uV} R M where
  obj A := Rep.of (action A.ρ U θ M hMU hθ)
  map f := Rep.ofHom (map U θ M hMU hθ f.hom)
  map_id A := by
    apply Rep.hom_ext
    exact map_id A.ρ U θ M hMU hθ
  map_comp f g := by
    apply Rep.hom_ext
    exact map_comp U θ M hMU hθ f.hom g.hom

section Smooth
variable [TopologicalSpace G]

/-- Smoothness descends from the continuous subgroup restriction and surjective quotient. -/
theorem isSmooth_action (ρ : Representation R G V) (U : Subgroup G) (θ : U →* Rˣ)
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U) (hθ : IsInvariant U M hMU θ)
    (hρ : IsSmooth ρ) : IsSmooth (action ρ U θ M hMU hθ) :=
  isSmooth_of_surjective (quotientMap ρ U θ M hMU hθ) (mk_surjective ρ U θ)
    (isSmooth_comp M.subtype continuous_subtype_val hρ)

/-- The localization of a bundled smooth representation, on the actual quotient carrier. -/
abbrev smoothObject (U : Subgroup G) (θ : U →* Rˣ) (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer U) (hθ : IsInvariant U M hMU θ)
    (A : SmoothRep.{uR, uG, uV} R G) : SmoothRep.{uR, uG, uV} R M :=
  SmoothRep.of (action A.representation U θ M hMU hθ)
    (isSmooth_action A.representation U θ M hMU hθ A.isSmooth)

/-- The smooth localization functor; both subgroups carry the induced topology. -/
def smoothFunctor (U : Subgroup G) (θ : U →* Rˣ) (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer U) (hθ : IsInvariant U M hMU θ) :
    SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uR, uG, uV} R M where
  obj A := smoothObject U θ M hMU hθ A
  map f := SmoothRep.ofHom (map U θ M hMU hθ (SmoothRep.hom f))
  map_id A := by
    change SmoothRep.ofHom (A := smoothObject U θ M hMU hθ A)
        (B := smoothObject U θ M hMU hθ A)
        (map U θ M hMU hθ (Representation.IntertwiningMap.id A.representation)) =
      SmoothRep.ofHom (Representation.IntertwiningMap.id _)
    rw [map_id]
  map_comp {A B C} f g := by
    change SmoothRep.ofHom (A := smoothObject U θ M hMU hθ A)
        (B := smoothObject U θ M hMU hθ C)
        (map U θ M hMU hθ ((SmoothRep.hom g).comp (SmoothRep.hom f))) =
      SmoothRep.ofHom ((map U θ M hMU hθ (SmoothRep.hom g)).comp
        (map U θ M hMU hθ (SmoothRep.hom f)))
    rw [map_comp]

end Smooth

/-- The trivial character is invariant under every normalizing subgroup. -/
theorem isInvariant_one (U M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U) :
    IsInvariant U M hMU (1 : U →* Rˣ) := fun _ _ => rfl

/-- With the trivial character, the relation submodule is the accepted untwisted one. -/
@[simp] theorem relations_one (ρ : Representation R G V) (U : Subgroup G) :
    relations ρ U (1 : U →* Rˣ) = Jacquet.relations ρ U := by
  simp [relations, Jacquet.relations, Representation.Coinvariants.ker]

/-- The concrete quotient equivalence with the existing untwisted coinvariants. -/
def trivialEquiv (ρ : Representation R G V) (U M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer U) :
    (action ρ U 1 M hMU (isInvariant_one U M hMU)).Equiv (Jacquet.action ρ U M hMU) where
  toLinearEquiv := Submodule.quotEquivOfEq _ _ (relations_one ρ U)
  isIntertwining' m := by
    apply hom_ext
    rfl

@[simp] theorem trivialEquiv_mk (ρ : Representation R G V) (U M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer U) (v : V) :
    trivialEquiv ρ U M hMU (mk ρ U 1 v) = Jacquet.mk ρ U v := rfl

/-- The comparison intertwining equivalence is natural for every ambient intertwiner. -/
theorem trivialEquiv_natural {ρ : Representation R G V} {σ : Representation R G W}
    (U M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U) (f : ρ.IntertwiningMap σ) :
    (Jacquet.map U M hMU f).comp (trivialEquiv ρ U M hMU).toIntertwiningMap =
      (trivialEquiv σ U M hMU).toIntertwiningMap.comp
        (map U 1 M hMU (isInvariant_one U M hMU) f) := by
  apply Representation.IntertwiningMap.ext
  exact hom_ext rfl

end Langlands.Jacquet.Localization
