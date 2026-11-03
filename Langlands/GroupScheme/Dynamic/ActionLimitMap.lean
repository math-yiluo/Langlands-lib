import Langlands.GroupScheme.Dynamic.Action
import Langlands.GroupScheme.Dynamic.Uniqueness

/-! # Fixed limits and the limit homomorphism for abstract automorphic actions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {G : GroupScheme S}
    (a : AutomorphicAction (Gm S).toGrp G)

/-- Choose a zero value of an orbit extension of a parabolic point. -/
def limit {T : Over S} (g : a.parabolic.carrier T) : T ⟶ G.X :=
  (a.exists_hasLimit g.2).choose

theorem hasLimit_limit {T : Over S} (g : a.parabolic.carrier T) :
    a.HasLimit g (a.limit g) :=
  (a.exists_hasLimit g.2).choose_spec

variable [IsSeparated G.X.hom]

/-- The limit of an abstract multiplicative-group orbit is fixed by the action. -/
theorem HasLimit.mem_centralizer {T : Over S} {g l : T ⟶ G.X}
    (hl : a.HasLimit g l) : l ∈ a.centralizer.carrier T := by
  obtain ⟨e, he, rfl⟩ := hl
  let s : (T ⊗ (Gm S).X) ⊗ AffineLine.scheme S ⟶ (Gm S).X := fst _ _ ≫ snd _ _
  have key : a.act s (fst T (Gm S).X ▷ AffineLine.scheme S ≫ e) =
      AffineLine.scale T ≫ e := by
    apply AffineLine.hom_ext_of_unitInclusion
    rw [AffineLine.whiskerLeft_unitInclusion_scale_assoc, he, a.naturality,
      whisker_exchange_assoc, he, a.whiskerRight_orbit]
    simp only [s, orbit, a.naturality, whiskerLeft_fst_assoc, lift_fst_assoc,
      lift_snd, a.act_mul_left, Category.assoc]
  have h0 := congrArg Dynamic.evalZero key
  have hact : Dynamic.evalZero
      (a.act s (fst T (Gm S).X ▷ AffineLine.scheme S ≫ e)) =
      a.orbit (Dynamic.evalZero e) := by
    unfold Dynamic.evalZero
    rw [a.naturality]
    simp only [s, lift_fst_assoc, Category.id_comp]
    change a.act (snd T (Gm S).X)
      (Dynamic.evalZero (fst T (Gm S).X ▷ AffineLine.scheme S ≫ e)) = _
    rw [Dynamic.evalZero_whiskerRight, orbit]
    rfl
  rw [hact] at h0
  rw [a.mem_centralizer]
  refine h0.trans ?_
  rw [Dynamic.evalZero, ← Category.assoc, AffineLine.lift_zeroSection_scale, Category.assoc]
  rfl

/-- The chosen limit agrees with every zero value of an orbit extension. -/
theorem limit_eq {T : Over S} {g : a.parabolic.carrier T} {l : T ⟶ G.X}
    (hl : a.HasLimit g l) : a.limit g = l := by
  obtain ⟨e, he, he0⟩ := a.hasLimit_limit g
  obtain ⟨e', he', he0'⟩ := hl
  have h : e = e' := AffineLine.hom_ext_of_unitInclusion (he.trans he'.symm)
  exact he0.symm.trans ((congrArg Dynamic.evalZero h).trans he0')

theorem limit_mem_centralizer {T : Over S} (g : a.parabolic.carrier T) :
    a.limit g ∈ a.centralizer.carrier T :=
  (a.hasLimit_limit g).mem_centralizer a

/-- Evaluation at zero is a natural group homomorphism from extending to fixed points. -/
def limitHom (T : Over S) : a.parabolic.carrier T →* a.centralizer.carrier T where
  toFun g := ⟨a.limit g, a.limit_mem_centralizer g⟩
  map_one' := Subtype.ext (a.limit_eq (a.hasLimit_of_mem_centralizer (one_mem _)))
  map_mul' g h := Subtype.ext (a.limit_eq ((a.hasLimit_limit g).mul a (a.hasLimit_limit h)))

@[simp] theorem limitHom_apply_coe (T : Over S) (g : a.parabolic.carrier T) :
    (a.limitHom T g : T ⟶ G.X) = a.limit g := rfl

/-- Existence of a limit is equivalent to the value of the limit homomorphism. -/
theorem hasLimit_iff_limitHom {T : Over S} {g l : T ⟶ G.X} :
    a.HasLimit g l ↔ ∃ hg : g ∈ a.parabolic.carrier T,
      (a.limitHom T ⟨g, hg⟩ : T ⟶ G.X) = l :=
  ⟨fun hl => ⟨hl.mem_parabolic a, a.limit_eq hl⟩,
    fun ⟨hg, hl⟩ => hl ▸ a.hasLimit_limit ⟨g, hg⟩⟩

/-- The limit homomorphisms commute with every change of test scheme. -/
theorem limitHom_comp {T T' : Over S} (b : T' ⟶ T) (g : a.parabolic.carrier T) :
    (a.limitHom T' ⟨b ≫ g, a.parabolic.comp_mem b g.2⟩ : T' ⟶ G.X) =
      b ≫ (a.limitHom T g : T ⟶ G.X) :=
  a.limit_eq ((a.hasLimit_limit g).whiskerRight a b)

/-- Inclusion of fixed points is a section of the limit homomorphism. -/
theorem limitHom_inclusion (T : Over S) (z : a.centralizer.carrier T) :
    a.limitHom T (Subgroup.inclusion (a.centralizer_le_parabolic T) z) = z :=
  Subtype.ext (a.limit_eq (a.hasLimit_of_mem_centralizer z.2))

theorem limitHom_surjective (T : Over S) : Function.Surjective (a.limitHom T) :=
  fun z => ⟨_, a.limitHom_inclusion T z⟩

/-- The kernel of the limit homomorphism is the identity-limit subgroup. -/
theorem ker_limitHom (T : Over S) :
    (a.limitHom T).ker = (a.unipotent.carrier T).subgroupOf (a.parabolic.carrier T) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_unipotent, hasLimit_iff_limitHom]
  constructor
  · intro h
    exact ⟨g.2, congrArg Subtype.val h⟩
  · rintro ⟨_, h⟩
    exact Subtype.ext h

/-- Dividing a parabolic point by its fixed limit gives an identity-limit point. -/
theorem mul_inv_limit_mem_unipotent {T : Over S} (g : a.parabolic.carrier T) :
    (g : T ⟶ G.X) * (a.limit g)⁻¹ ∈ a.unipotent.carrier T := by
  have h := (a.hasLimit_limit g).mul a
    ((a.hasLimit_of_mem_centralizer (a.limit_mem_centralizer g)).inv a)
  rwa [mul_inv_cancel] at h

end Langlands.GroupScheme.AutomorphicAction
