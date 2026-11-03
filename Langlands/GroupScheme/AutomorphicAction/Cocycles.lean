import Langlands.GroupScheme.AutomorphicAction

/-! # Actual cocycle morphisms and their all-test conjugation orbit -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {H G : GroupScheme S} (a : AutomorphicAction H G)

/-- A relative cocycle is an actual morphism on `T × H`, with the normalized cocycle
identities on every test scheme. -/
structure Cocycle (T : Over S) where
  hom : T ⊗ H.X ⟶ G.X
  one : ∀ {V : Over S} (b : V ⟶ T), lift b (1 : V ⟶ H.X) ≫ hom = 1
  mul : ∀ {V : Over S} (b : V ⟶ T) (h h' : V ⟶ H.X),
    lift b (h * h') ≫ hom =
      (lift b h ≫ hom) * a.act h (lift b h' ≫ hom)

namespace Cocycle

variable {a} {T T' T'' : Over S}

@[ext]
theorem ext {c d : a.Cocycle T} (h : c.hom = d.hom) : c = d := by
  cases c
  cases d
  congr

/-- Evaluation of an actual relative cocycle at a test point. -/
def eval (c : a.Cocycle T) {V : Over S} (b : V ⟶ T) (h : V ⟶ H.X) :
    V ⟶ G.X :=
  lift b h ≫ c.hom

theorem eval_naturality (c : a.Cocycle T) {V V' : Over S} (v : V' ⟶ V)
    (b : V ⟶ T) (h : V ⟶ H.X) :
    v ≫ c.eval b h = c.eval (v ≫ b) (v ≫ h) := by
  simp only [eval, ← Category.assoc, comp_lift]

@[simp]
theorem eval_one (c : a.Cocycle T) {V : Over S} (b : V ⟶ T) :
    c.eval b (1 : V ⟶ H.X) = 1 :=
  c.one b

theorem eval_mul (c : a.Cocycle T) {V : Over S} (b : V ⟶ T) (h h' : V ⟶ H.X) :
    c.eval b (h * h') = c.eval b h * a.act h (c.eval b h') :=
  c.mul b h h'

/-- All-test evaluation determines a cocycle. -/
theorem eval_ext {c d : a.Cocycle T}
    (h : ∀ (V : Over S) (b : V ⟶ T) (t : V ⟶ H.X), c.eval b t = d.eval b t) :
    c = d := by
  apply ext
  simpa only [eval, lift_fst_snd, Category.id_comp] using
    h (T ⊗ H.X) (fst T H.X) (snd T H.X)

/-- Restriction of a relative cocycle along a morphism of parameter schemes. -/
def restrict (b : T' ⟶ T) (c : a.Cocycle T) : a.Cocycle T' where
  hom := (b ▷ H.X) ≫ c.hom
  one v := by
    simpa only [Category.assoc, lift_whiskerRight_assoc] using c.one (v ≫ b)
  mul v h h' := by
    simpa only [Category.assoc, lift_whiskerRight_assoc] using c.mul (v ≫ b) h h'

@[simp]
theorem eval_restrict (b : T' ⟶ T) (c : a.Cocycle T) {V : Over S}
    (v : V ⟶ T') (h : V ⟶ H.X) :
    (restrict b c).eval v h = c.eval (v ≫ b) h := by
  simp only [eval, restrict, lift_whiskerRight_assoc]

@[simp]
theorem restrict_id (c : a.Cocycle T) : restrict (𝟙 T) c = c := by
  apply eval_ext
  intro V b h
  simp

theorem restrict_comp (b : T' ⟶ T) (b' : T'' ⟶ T') (c : a.Cocycle T) :
    restrict (b' ≫ b) c = restrict b' (restrict b c) := by
  apply eval_ext
  intro V v h
  simp only [eval_restrict, Category.assoc]

/-- The cocycle of the canonical section of the semidirect projection. -/
def trivial (T : Over S) : a.Cocycle T where
  hom := 1
  one b := MonObj.comp_one _
  mul b h h' := by simp only [MonObj.comp_one, a.act_one, mul_one]

@[simp]
theorem eval_trivial {V : Over S} (b : V ⟶ T) (h : V ⟶ H.X) :
    (trivial T : a.Cocycle T).eval b h = 1 :=
  MonObj.comp_one _

@[simp]
theorem restrict_trivial (b : T' ⟶ T) :
    restrict b (trivial T : a.Cocycle T) = trivial T' := by
  apply eval_ext
  intro V v h
  simp

/-- Conjugation of a section, written in cocycle coordinates. -/
def conjugate (g : T ⟶ G.X) (c : a.Cocycle T) : a.Cocycle T where
  hom := (fst T H.X ≫ g) * c.hom *
    a.act (snd T H.X) (fst T H.X ≫ g)⁻¹
  one b := by
    simp only [MonObj.comp_mul, GrpObj.comp_inv, a.naturality,
      lift_fst_assoc, lift_snd, c.one, a.act_one_left]
    simp
  mul b h h' := by
    simp only [MonObj.comp_mul, GrpObj.comp_inv, a.naturality,
      lift_fst_assoc, lift_snd, c.mul, a.act_mul_left, a.act_mul_right, a.act_inv]
    group

@[simp]
theorem eval_conjugate (g : T ⟶ G.X) (c : a.Cocycle T) {V : Over S}
    (b : V ⟶ T) (h : V ⟶ H.X) :
    (conjugate g c).eval b h =
      (b ≫ g) * c.eval b h * a.act h (b ≫ g)⁻¹ := by
  simp only [eval, conjugate, MonObj.comp_mul, GrpObj.comp_inv,
    a.naturality, lift_fst_assoc, lift_snd]

@[simp]
theorem conjugate_one (c : a.Cocycle T) :
    conjugate (1 : T ⟶ G.X) c = c := by
  apply eval_ext
  intro V b h
  simp

theorem conjugate_mul (g g' : T ⟶ G.X) (c : a.Cocycle T) :
    conjugate (g * g') c = conjugate g (conjugate g' c) := by
  apply eval_ext
  intro V b h
  simp only [eval_conjugate, MonObj.comp_mul, mul_inv_rev, a.act_mul_right]
  group

theorem restrict_conjugate (b : T' ⟶ T) (g : T ⟶ G.X) (c : a.Cocycle T) :
    restrict b (conjugate g c) = conjugate (b ≫ g) (restrict b c) := by
  apply eval_ext
  intro V v h
  simp only [eval_restrict, eval_conjugate, Category.assoc]

end Cocycle

/-- The functor of actual cocycle morphisms, with restriction of the parameter scheme. -/
def cocycleFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := a.Cocycle T.unop
  map b := ↾fun c => Cocycle.restrict (a := a) b.unop c
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro c
    exact Cocycle.restrict_id c
  map_comp b b' := by
    apply ConcreteCategory.hom_ext
    intro c
    exact Cocycle.restrict_comp b.unop b'.unop c

/-- The orbit of the canonical section, in cocycle coordinates. -/
def coboundary {T : Over S} (g : T ⟶ G.X) : a.Cocycle T :=
  Cocycle.conjugate g (Cocycle.trivial T)

@[simp]
theorem eval_coboundary {T V : Over S} (g : T ⟶ G.X) (b : V ⟶ T) (h : V ⟶ H.X) :
    (a.coboundary g).eval b h = (b ≫ g) * a.act h (b ≫ g)⁻¹ := by
  simp only [coboundary, Cocycle.eval_conjugate, Cocycle.eval_trivial, mul_one]

@[simp]
theorem restrict_coboundary {T T' : Over S} (b : T' ⟶ T) (g : T ⟶ G.X) :
    Cocycle.restrict b (a.coboundary g) = a.coboundary (b ≫ g) := by
  simp only [coboundary, Cocycle.restrict_conjugate, Cocycle.restrict_trivial]

/-- The canonical cocycle orbit is a natural transformation on all schemes over the base. -/
def cocycleOrbit : yoneda.obj G.X ⟶ a.cocycleFunctor where
  app T := ↾fun g => a.coboundary g
  naturality {T T'} b := by
    apply ConcreteCategory.hom_ext
    intro g
    exact (a.restrict_coboundary b.unop g).symm

/-- Two points give the same canonical cocycle exactly when their difference is fixed after
every refinement. This is the full right-coset fiber equation. -/
theorem coboundary_eq_iff {T : Over S} (g g' : T ⟶ G.X) :
    a.coboundary g = a.coboundary g' ↔
      g⁻¹ * g' ∈ a.fixedSubgroup.carrier T := by
  constructor
  · intro he V b h
    have hv := congrArg (fun c : a.Cocycle T => c.eval b h) he
    simp only [eval_coboundary, a.act_inv] at hv
    simp only [MonObj.comp_mul, GrpObj.comp_inv, a.act_mul_right, a.act_inv]
    calc
      (a.act h (b ≫ g))⁻¹ * a.act h (b ≫ g') =
          (b ≫ g)⁻¹ * ((b ≫ g) * (a.act h (b ≫ g))⁻¹) * a.act h (b ≫ g') := by
            group
      _ = (b ≫ g)⁻¹ * ((b ≫ g') * (a.act h (b ≫ g'))⁻¹) * a.act h (b ≫ g') := by
            rw [hv]
      _ = (b ≫ g)⁻¹ * (b ≫ g') := by group
  · intro hfix
    apply Cocycle.eval_ext
    intro V b h
    have hv := hfix V b h
    simp only [MonObj.comp_mul, GrpObj.comp_inv, a.act_mul_right, a.act_inv] at hv
    simp only [eval_coboundary, a.act_inv]
    calc
      (b ≫ g) * (a.act h (b ≫ g))⁻¹ =
          (b ≫ g) * ((a.act h (b ≫ g))⁻¹ * a.act h (b ≫ g')) *
            (a.act h (b ≫ g'))⁻¹ := by group
      _ = (b ≫ g) * ((b ≫ g)⁻¹ * (b ≫ g')) * (a.act h (b ≫ g'))⁻¹ := by rw [hv]
      _ = (b ≫ g') * (a.act h (b ≫ g'))⁻¹ := by group

end Langlands.GroupScheme.AutomorphicAction
