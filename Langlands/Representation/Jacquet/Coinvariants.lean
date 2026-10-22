import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Jacquet coinvariants and actions of normalizing subgroups

The quotient is Mathlib's actual quotient by the span of `ρ n v - v`.
The acting subgroup need only normalize the subgroup of coinvariants.
-/

namespace Langlands.Jacquet

universe uR uG uV uW uX

variable {R : Type uR} {G : Type uG}
variable [CommRing R] [Group G]
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]
variable [AddCommGroup X] [Module R X]

/-- The span of the actual coinvariant relations for a subgroup. -/
abbrev relations (ρ : Representation R G V) (N : Subgroup G) : Submodule R V :=
  Representation.Coinvariants.ker (ρ.comp N.subtype)

/-- The actual quotient module by the subgroup's coinvariant relations. -/
abbrev Coinvariants (ρ : Representation R G V) (N : Subgroup G) :=
  Representation.Coinvariants (ρ.comp N.subtype)

/-- The canonical linear quotient map. -/
abbrev mk (ρ : Representation R G V) (N : Subgroup G) :
    V →ₗ[R] Coinvariants ρ N :=
  Representation.Coinvariants.mk (ρ.comp N.subtype)

theorem relations_eq_span (ρ : Representation R G V) (N : Subgroup G) :
    relations ρ N =
      Submodule.span R (Set.range fun nv : N × V => ρ nv.1 nv.2 - nv.2) := rfl

theorem sub_mem_relations (ρ : Representation R G V) (N : Subgroup G)
    (n : N) (v : V) : ρ n v - v ∈ relations ρ N :=
  Representation.Coinvariants.sub_mem_ker n v

@[simp]
theorem mk_apply_subgroup (ρ : Representation R G V) (N : Subgroup G)
    (n : N) (v : V) : mk ρ N (ρ n v) = mk ρ N v :=
  Representation.Coinvariants.mk_self_apply _ n v

theorem mk_surjective (ρ : Representation R G V) (N : Subgroup G) :
    Function.Surjective (mk ρ N) :=
  Representation.Coinvariants.mk_surjective _

@[simp]
theorem mk_eq_zero (ρ : Representation R G V) (N : Subgroup G) (v : V) :
    mk ρ N v = 0 ↔ v ∈ relations ρ N :=
  Representation.Coinvariants.mk_eq_zero _

theorem ker_mk (ρ : Representation R G V) (N : Subgroup G) :
    LinearMap.ker (mk ρ N) = relations ρ N := by
  ext v
  exact mk_eq_zero ρ N v

/-- Conjugation sends a generating relation to another generating relation. -/
theorem relations_stable (ρ : Representation R G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (m : M) :
    relations ρ N ≤ (relations ρ N).comap (ρ m) := by
  apply Submodule.span_le.2
  rintro _ ⟨⟨n, v⟩, rfl⟩
  have hn : (m : G) * n * (m : G)⁻¹ ∈ N :=
    ((Subgroup.mem_normalizer_iff.mp (hMN m.property)) n).mp n.property
  change ρ m (ρ n v - v) ∈ relations ρ N
  exact Representation.Coinvariants.mem_ker_of_eq
    (ρ := ρ.comp N.subtype) ⟨(m : G) * n * (m : G)⁻¹, hn⟩ (ρ m v) _ (by simp)

/-- The relation submodule as a subrepresentation of the normalizing subgroup. -/
def relationsSubrepresentation (ρ : Representation R G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) : Subrepresentation (ρ.comp M.subtype) where
  toSubmodule := relations ρ N
  apply_mem_toSubmodule m := relations_stable ρ N M hMN m

/-- The descended action of a subgroup normalizing `N`, before normalization. -/
noncomputable def action (ρ : Representation R G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) : Representation R M (Coinvariants ρ N) :=
  Representation.quotient (ρ.comp M.subtype) (relations ρ N)
    (relations_stable ρ N M hMN)

@[simp]
theorem action_mk (ρ : Representation R G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (m : M) (v : V) :
    action ρ N M hMN m (mk ρ N v) = mk ρ N (ρ m v) := rfl

/-- The quotient map is equivariant for the normalizing subgroup. -/
noncomputable def quotientMap (ρ : Representation R G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) :
    Representation.IntertwiningMap (ρ.comp M.subtype) (action ρ N M hMN) where
  toLinearMap := mk ρ N
  isIntertwining' _ := rfl

/-- Restrict an ambient intertwiner to any subgroup. -/
def restrictMap {ρ : Representation R G V} {σ : Representation R G W}
    (f : ρ.IntertwiningMap σ) (H : Subgroup G) :
    Representation.IntertwiningMap (ρ.comp H.subtype) (σ.comp H.subtype) where
  toLinearMap := f.toLinearMap
  isIntertwining' h := f.isIntertwining' h

/-- An ambient intertwiner induces an equivariant map on the actual quotients. -/
noncomputable def map {ρ : Representation R G V} {σ : Representation R G W}
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (f : ρ.IntertwiningMap σ) :
    (action ρ N M hMN).IntertwiningMap (action σ N M hMN) where
  toLinearMap := Representation.Coinvariants.map _ _ (restrictMap f N)
  isIntertwining' m := by
    apply Representation.Coinvariants.hom_ext
    ext v
    change mk σ N (f (ρ m v)) = mk σ N (σ m (f v))
    exact congrArg (mk σ N) (Representation.IntertwiningMap.isIntertwining ρ σ f m v)

@[simp]
theorem map_mk {ρ : Representation R G V} {σ : Representation R G W}
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (f : ρ.IntertwiningMap σ) (v : V) :
    map N M hMN f (mk ρ N v) = mk σ N (f v) := rfl

theorem map_comp_quotientMap {ρ : Representation R G V} {σ : Representation R G W}
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (f : ρ.IntertwiningMap σ) :
    (map N M hMN f).comp (quotientMap ρ N M hMN) =
      (quotientMap σ N M hMN).comp (restrictMap f M) := by
  ext v
  rfl

@[simp]
theorem map_id (ρ : Representation R G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) :
    map N M hMN (Representation.IntertwiningMap.id ρ) =
      Representation.IntertwiningMap.id (action ρ N M hMN) := by
  apply Representation.IntertwiningMap.ext
  apply Representation.Coinvariants.hom_ext
  rfl

@[simp]
theorem map_comp {ρ : Representation R G V} {σ : Representation R G W}
    {τ : Representation R G X} (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
    map N M hMN (g.comp f) = (map N M hMN g).comp (map N M hMN f) := by
  apply Representation.IntertwiningMap.ext
  apply Representation.Coinvariants.hom_ext
  rfl

/-- A linear map constant on `N`-orbits factors through the quotient. -/
def lift (ρ : Representation R G V) (N : Subgroup G) (f : V →ₗ[R] W)
    (hf : ∀ n : N, f ∘ₗ ρ n = f) : Coinvariants ρ N →ₗ[R] W :=
  Representation.Coinvariants.lift _ f hf

@[simp]
theorem lift_mk (ρ : Representation R G V) (N : Subgroup G) (f : V →ₗ[R] W)
    (hf : ∀ n : N, f ∘ₗ ρ n = f) (v : V) :
    lift ρ N f hf (mk ρ N v) = f v := rfl

theorem lift_unique (ρ : Representation R G V) (N : Subgroup G) (f : V →ₗ[R] W)
    (hf : ∀ n : N, f ∘ₗ ρ n = f) (g : Coinvariants ρ N →ₗ[R] W)
    (hg : g ∘ₗ mk ρ N = f) : g = lift ρ N f hf :=
  Representation.Coinvariants.hom_ext hg

end Langlands.Jacquet
