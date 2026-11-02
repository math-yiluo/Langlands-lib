import Langlands.GroupScheme.Dynamic.Decomposition
import Langlands.GroupScheme.Dynamic.Uniqueness
import Mathlib.GroupTheory.SemidirectProduct

/-! # The limit homomorphism and `P(χ) ≅ U(χ) ⋊ Z(χ)` for separated group schemes

Let `G` be a group scheme over a scheme `S` whose structure morphism is separated, and let
`χ : 𝔾_{m,S} ⟶ G` be a cocharacter. On every test scheme `T` over `S`, taking the limit at zero
of the conjugation orbit is a group homomorphism `P(χ)(T) →* Z(χ)(T)`, natural in `T`. Its kernel
is `U(χ)(T)`, and the inclusion `Z(χ)(T) ≤ P(χ)(T)` is a section of it. The multiplication map
`(u, z) ↦ u * z` is an isomorphism from the semidirect product `U(χ)(T) ⋊ Z(χ)(T)`, for the
conjugation action of `Z(χ)(T)` on `U(χ)(T)`, onto `P(χ)(T)`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S} (χ : (Gm S).toGrp ⟶ G)

/-- Limits are compatible with restriction along a morphism of test schemes. -/
theorem HasLimit.comp {T T' : Over S} (a : T' ⟶ T) {g l : T ⟶ G.X} (hl : HasLimit χ g l) :
    HasLimit χ (a ≫ g) (a ≫ l) := by
  obtain ⟨e, he, rfl⟩ := hl
  exact ⟨a ▷ AffineLine.scheme S ≫ e, he.whiskerRight χ a, evalZero_whiskerRight a e⟩

/-- A limit at zero of the conjugation orbit of a point of `P(χ)`, chosen among its limits; for
separated `G` it is the unique limit (`limit_eq`). -/
def limit {T : Over S} (g : (parabolic χ).carrier T) : T ⟶ G.X :=
  (exists_hasLimit χ g.2).choose

theorem hasLimit_limit {T : Over S} (g : (parabolic χ).carrier T) :
    HasLimit χ g (limit χ g) :=
  (exists_hasLimit χ g.2).choose_spec

/-- The points of `Z(χ)` normalize the points of `U(χ)` in `G(T)`. -/
theorem centralizer_le_normalizer_unipotent (T : Over S) :
    (centralizer χ).carrier T ≤
      Subgroup.normalizer (((unipotent χ).carrier T : Subgroup (T ⟶ G.X)) : Set (T ⟶ G.X)) := by
  intro z hz u
  have hzP := centralizer_le_parabolic χ T hz
  refine ⟨fun hu => conj_mem_unipotent χ hzP hu, fun hu => ?_⟩
  have h := conj_mem_unipotent χ (inv_mem hzP) hu
  rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
    mul_one] at h

/-- The conjugation action of `Z(χ)(T)` on `U(χ)(T)`. -/
abbrev centralizerConj (T : Over S) :
    (centralizer χ).carrier T →* MulAut ((unipotent χ).carrier T) :=
  ((unipotent χ).carrier T).normalizerMonoidHom.comp
    (Subgroup.inclusion (centralizer_le_normalizer_unipotent χ T))

theorem centralizerConj_apply_coe (T : Over S) (z : (centralizer χ).carrier T)
    (x : (unipotent χ).carrier T) :
    (centralizerConj χ T z x : T ⟶ G.X) = z * x * z⁻¹ :=
  rfl

/-- The product of a point of `U(χ)` and a point of `Z(χ)` lies in `P(χ)`. -/
theorem mul_mem_parabolic {T : Over S} (x : (unipotent χ).carrier T)
    (z : (centralizer χ).carrier T) : (x : T ⟶ G.X) * z ∈ (parabolic χ).carrier T :=
  mul_mem (unipotent_le_parabolic χ T x.2) (centralizer_le_parabolic χ T z.2)

variable [IsSeparated G.X.hom]

theorem limit_eq {T : Over S} {g : (parabolic χ).carrier T} {l : T ⟶ G.X}
    (hl : HasLimit χ g l) : limit χ g = l :=
  (hasLimit_limit χ g).unique χ hl

theorem limit_mem_centralizer {T : Over S} (g : (parabolic χ).carrier T) :
    limit χ g ∈ (centralizer χ).carrier T :=
  (hasLimit_limit χ g).mem_centralizer χ

/-- Conrad–Gabber–Prasad, Lemma 2.1.5, on the points over a test scheme `T`: the limit
homomorphism `P(χ)(T) →* Z(χ)(T)`. -/
def limitHom (T : Over S) : (parabolic χ).carrier T →* (centralizer χ).carrier T where
  toFun g := ⟨limit χ g, limit_mem_centralizer χ g⟩
  map_one' := Subtype.ext (limit_eq χ (hasLimit_of_mem_centralizer χ (one_mem _)))
  map_mul' g h := Subtype.ext (limit_eq χ ((hasLimit_limit χ g).mul χ (hasLimit_limit χ h)))

@[simp] theorem limitHom_apply_coe (T : Over S) (g : (parabolic χ).carrier T) :
    (limitHom χ T g : T ⟶ G.X) = limit χ g :=
  rfl

/-- A point `g` has limit `l` exactly when `g` lies in `P(χ)` and the limit homomorphism sends it
to `l`. -/
theorem hasLimit_iff_limitHom {T : Over S} {g l : T ⟶ G.X} :
    HasLimit χ g l ↔ ∃ hg : g ∈ (parabolic χ).carrier T, (limitHom χ T ⟨g, hg⟩ : T ⟶ G.X) = l :=
  ⟨fun hl => ⟨hl.mem_parabolic χ, limit_eq χ hl⟩, fun ⟨hg, hl⟩ => hl ▸ hasLimit_limit χ ⟨g, hg⟩⟩

/-- The limit homomorphism is natural in the test scheme. -/
theorem limitHom_comp {T T' : Over S} (a : T' ⟶ T) (g : (parabolic χ).carrier T) :
    (limitHom χ T' ⟨a ≫ g, (parabolic χ).comp_mem a g.2⟩ : T' ⟶ G.X) =
      a ≫ (limitHom χ T g : T ⟶ G.X) :=
  limit_eq χ ((hasLimit_limit χ g).comp χ a)

/-- On `Z(χ)` the limit homomorphism is the identity: the inclusion `Z(χ)(T) ≤ P(χ)(T)` is a
section of it. -/
theorem limitHom_inclusion (T : Over S) (z : (centralizer χ).carrier T) :
    limitHom χ T (Subgroup.inclusion (centralizer_le_parabolic χ T) z) = z :=
  Subtype.ext (limit_eq χ (hasLimit_of_mem_centralizer χ z.2))

theorem limitHom_comp_inclusion (T : Over S) :
    (limitHom χ T).comp (Subgroup.inclusion (centralizer_le_parabolic χ T)) = MonoidHom.id _ :=
  MonoidHom.ext (limitHom_inclusion χ T)

theorem limitHom_surjective (T : Over S) : Function.Surjective (limitHom χ T) :=
  fun z => ⟨_, limitHom_inclusion χ T z⟩

/-- Conrad–Gabber–Prasad, Lemma 2.1.5: `U(χ)(T)` is the kernel of the limit homomorphism. -/
theorem ker_limitHom (T : Over S) :
    (limitHom χ T).ker = ((unipotent χ).carrier T).subgroupOf ((parabolic χ).carrier T) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_unipotent, hasLimit_iff_limitHom]
  constructor
  · intro h
    exact ⟨g.2, congrArg Subtype.val h⟩
  · rintro ⟨_, h⟩
    exact Subtype.ext h

theorem limit_eq_one_iff {T : Over S} (g : (parabolic χ).carrier T) :
    limit χ g = 1 ↔ (g : T ⟶ G.X) ∈ (unipotent χ).carrier T := by
  rw [← Subgroup.mem_subgroupOf, ← ker_limitHom, MonoidHom.mem_ker, Subtype.ext_iff]
  rfl

/-- Conrad–Gabber–Prasad, Proposition 2.1.8(2), on the points over a test scheme `T`: the points
of `U(χ)` and `Z(χ)` are complementary subgroups of the points of `P(χ)`. -/
theorem isComplement'_unipotent_centralizer_of_isSeparated (T : Over S) :
    (((unipotent χ).carrier T).subgroupOf ((parabolic χ).carrier T)).IsComplement'
      (((centralizer χ).carrier T).subgroupOf ((parabolic χ).carrier T)) :=
  isComplement'_unipotent_centralizer χ (fun _ _ _ _ hl hl' => hl.unique χ hl')
    (fun _ _ _ hl => hl.mem_centralizer χ) T

/-- `g * (lim g)⁻¹` lies in `U(χ)` for every point `g` of `P(χ)`. -/
theorem mul_inv_limit_mem_unipotent {T : Over S} (g : (parabolic χ).carrier T) :
    (g : T ⟶ G.X) * (limit χ g)⁻¹ ∈ (unipotent χ).carrier T := by
  have h := (hasLimit_limit χ g).mul χ
    (hasLimit_of_mem_centralizer χ (limit_mem_centralizer χ g)).inv
  rwa [mul_inv_cancel] at h

theorem limit_mul {T : Over S} (x : (unipotent χ).carrier T) (z : (centralizer χ).carrier T) :
    limit χ ⟨_, mul_mem_parabolic χ x z⟩ = z := by
  apply limit_eq
  have h := (x.2 : HasLimit χ _ 1).mul χ (hasLimit_of_mem_centralizer χ z.2)
  rwa [one_mul] at h

/-- Conrad–Gabber–Prasad, Proposition 2.1.8(2), on the points over a test scheme `T`: the
multiplication map `(u, z) ↦ u * z` is an isomorphism from the semidirect product
`U(χ)(T) ⋊ Z(χ)(T)` onto `P(χ)(T)`, with inverse `g ↦ (g * (lim g)⁻¹, lim g)`. -/
def semidirectEquiv (T : Over S) :
    (unipotent χ).carrier T ⋊[centralizerConj χ T] (centralizer χ).carrier T ≃*
      (parabolic χ).carrier T where
  toFun x := ⟨x.left * x.right, mul_mem_parabolic χ x.left x.right⟩
  invFun g := ⟨⟨_, mul_inv_limit_mem_unipotent χ g⟩, limitHom χ T g⟩
  left_inv x := by
    have h := limit_mul χ x.left x.right
    refine SemidirectProduct.ext (Subtype.ext ?_) (Subtype.ext h)
    change (x.left : T ⟶ G.X) * (x.right : T ⟶ G.X) * (limit χ _)⁻¹ = (x.left : T ⟶ G.X)
    rw [h, mul_inv_cancel_right]
  right_inv g := Subtype.ext (inv_mul_cancel_right _ _)
  map_mul' x y := by
    apply Subtype.ext
    change (x.left : T ⟶ G.X) * (x.right * y.left * (x.right : T ⟶ G.X)⁻¹) * (x.right * y.right) =
      x.left * x.right * (y.left * y.right)
    group

@[simp] theorem semidirectEquiv_apply_coe (T : Over S)
    (x : (unipotent χ).carrier T ⋊[centralizerConj χ T] (centralizer χ).carrier T) :
    (semidirectEquiv χ T x : T ⟶ G.X) = x.left * x.right :=
  rfl

@[simp] theorem semidirectEquiv_symm_apply_left_coe (T : Over S) (g : (parabolic χ).carrier T) :
    (((semidirectEquiv χ T).symm g).left : T ⟶ G.X) = g * (limit χ g)⁻¹ :=
  rfl

@[simp] theorem semidirectEquiv_symm_apply_right (T : Over S) (g : (parabolic χ).carrier T) :
    ((semidirectEquiv χ T).symm g).right = limitHom χ T g :=
  rfl

/-- Under the semidirect product isomorphism, the limit homomorphism is the projection to
`Z(χ)(T)`. -/
theorem limitHom_comp_semidirectEquiv (T : Over S) :
    (limitHom χ T).comp (semidirectEquiv χ T).toMonoidHom = SemidirectProduct.rightHom :=
  MonoidHom.ext fun x => Subtype.ext (limit_mul χ x.left x.right)

end Langlands.GroupScheme.Dynamic
