import Langlands.GroupScheme.Rational.SteinbergRootProduct

/-! # Supplied merged-root data and Steinberg's modified ordered morphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

namespace Langlands.GroupScheme

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- Supplied additive coordinates on one whole intrinsic root subgroup, for an arbitrary
root index, with the all-test torus-equivariance law. No Lie normalization is included. -/
structure RootParametrization (α : p.rootIndex) where
  hom : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G
  represents : (RelativeRoot.subgroup p.inclusion (p.rootDatum.root α)).IsRepresentedBy hom
  isClosedSubgroup : IsClosedSubgroup hom
  torus_equivariant : ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ p.torus.X)
    (c : Γ(T.left, ⊤)),
    (t ≫ p.inclusion.hom.hom) *
        (VectorGroup.scalarPoint (CommRingCat.of k) T c ≫ hom.hom.hom) *
        (t ≫ p.inclusion.hom.hom)⁻¹ =
      VectorGroup.scalarPoint (CommRingCat.of k) T
        (VectorGroup.charValue (p.rootDatum.root α) T t * c) ≫ hom.hom.hom

/-- A supplied rational representative and actual torus automorphism realizing the
reflection in an arbitrary root, with the Library's contravariant character convention. -/
structure ReflectionRepresentative (α : p.rootIndex) where
  point : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X
  torusAut : p.torus ≅ p.torus
  normalizes : IsNormalizingPoint p.inclusion point torusAut
  characterAut_eq : characterAut torusAut = p.rootDatum.reflection α

/-- The actual coroot cocharacter of the root datum, followed by the torus inclusion. -/
def corootHom (α : p.rootIndex) : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G :=
  CommGroupScheme.groupHom (p.rootDatum.coroot α) ≫ p.inclusion

theorem corootHom_hom_hom (α : p.rootIndex) :
    (p.corootHom α).hom.hom =
      (CommGroupScheme.groupHom (p.rootDatum.coroot α)).hom.hom ≫ p.inclusion.hom.hom :=
  rfl

variable {p}

/-- A normalized simple-root parametrization, with its Lie normalization forgotten. -/
def NormalizedRootParametrization.toRootParametrization {a : p.base.support}
    (x : p.NormalizedRootParametrization a) : p.RootParametrization a where
  hom := x.hom
  represents := x.represents
  isClosedSubgroup := x.isClosedSubgroup
  torus_equivariant := x.torus_equivariant

/-- A simple-reflection representative, regarded as a representative for its root index. -/
def SimpleReflectionRepresentative.toReflectionRepresentative {a : p.base.support}
    (n : p.SimpleReflectionRepresentative a) : p.ReflectionRepresentative a where
  point := n.point
  torusAut := n.torusAut
  normalizes := n.normalizes
  characterAut_eq := n.characterAut_eq

namespace RootParametrization

variable {α : p.rootIndex} (x : p.RootParametrization α)

/-- Evaluate the root map at a global function, using standard additive coordinates. -/
def point (T : Over (Spec (CommRingCat.of k))) (c : Γ(T.left, ⊤)) : T ⟶ G.X :=
  VectorGroup.scalarPoint (CommRingCat.of k) T c ≫ x.hom.hom.hom

/-- Evaluation of a supplied root parametrization is natural on every test. -/
theorem point_comp {T W : Over (Spec (CommRingCat.of k))} (f : W ⟶ T)
    (c : Γ(T.left, ⊤)) :
    f ≫ x.point T c = x.point W (f.left.appTop c) := by
  rw [point, ← Category.assoc, VectorGroup.scalarPoint_comp, point]

/-- The image is the whole intrinsic root subgroup on every scheme test. -/
theorem mem_rootSubgroup_iff (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) :
    g ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root α)).carrier T ↔
      ∃ c : Γ(T.left, ⊤), x.point T c = g := by
  rw [← x.represents.2, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨(VectorGroup.coordinates (CommRingCat.of k) 1 T v).toAdd 0, ?_⟩
    change VectorGroup.scalarPoint (CommRingCat.of k) T _ ≫ x.hom.hom.hom =
      v ≫ x.hom.hom.hom
    apply congrArg (fun z : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X =>
      z ≫ x.hom.hom.hom)
    apply VectorGroup.points_ext
    intro j
    rw [VectorGroup.coordinates_scalarPoint]
    exact congrArg (fun i => (VectorGroup.coordinates (CommRingCat.of k) 1 T v).toAdd i)
      (Subsingleton.elim 0 j)
  · rintro ⟨c, rfl⟩
    exact ⟨VectorGroup.scalarPoint (CommRingCat.of k) T c, rfl⟩

/-- The zero coordinate gives the identity point. -/
@[simp]
theorem point_zero (T : Over (Spec (CommRingCat.of k))) : x.point T 0 = 1 := by
  have h : VectorGroup.scalarPoint (CommRingCat.of k) T 0 = 1 := by
    apply VectorGroup.points_ext
    intro j
    rw [VectorGroup.coordinates_scalarPoint, map_one, toAdd_one, Pi.zero_apply]
  rw [point, h, MonObj.one_comp]

/-- The root map is injective on the points of every test, since it is a monomorphism. -/
theorem point_injective (T : Over (Spec (CommRingCat.of k))) :
    Function.Injective (x.point T) := by
  intro c c' h
  have : Mono x.hom.hom.hom := x.represents.1
  have h' := (cancel_mono x.hom.hom.hom).1 h
  have := congrArg (fun z => (VectorGroup.coordinates (CommRingCat.of k) 1 T z).toAdd 0) h'
  simpa only [VectorGroup.coordinates_scalarPoint] using this

theorem point_eq_one_iff (T : Over (Spec (CommRingCat.of k))) (c : Γ(T.left, ⊤)) :
    x.point T c = 1 ↔ c = 0 := by
  rw [← x.point_zero T]
  exact (x.point_injective T).eq_iff

/-- The rational point with standard additive coordinate `c ∈ k`. -/
def rationalPoint (c : k) : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X :=
  x.point _ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)

/-- On a test `T`, the restricted rational point has the image of `c` as its coordinate. -/
theorem toUnit_comp_rationalPoint (T : Over (Spec (CommRingCat.of k))) (c : k) :
    toUnit T ≫ x.rationalPoint c =
      x.point T (T.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) := by
  have h : (toUnit T).left = T.hom := by simp
  refine (x.point_comp (toUnit T) _).trans ?_
  rw [h]

/-- A nonzero scalar gives a nonidentity rational point of the root subgroup. -/
theorem rationalPoint_ne_one {c : k} (hc : c ≠ 0) : x.rationalPoint c ≠ 1 := by
  intro h
  rw [rationalPoint, point_eq_one_iff] at h
  apply hc
  simpa using congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom h

end RootParametrization

section OrderedProduct

variable {r : ℕ} (f : Fin r → p.base.support)
    (x : p.NormalizedSimpleRootParametrizations)
    (n : p.SimpleReflectionRepresentatives)

omit [IsAffineHom G.X.hom] in
private theorem comp_list_prod {T W : Over (Spec (CommRingCat.of k))} (g : W ⟶ T)
    (l : List (T ⟶ G.X)) :
    g ≫ l.prod = (l.map (fun h => g ≫ h)).prod := by
  induction l with
  | nil => simp
  | cons h l ih => simp only [List.prod_cons, List.map_cons, MonObj.comp_mul, ih]

/-- The ordered product of `x_(f j)(c_j) n_(f j)` for an arbitrary finite list `f` of
simple roots, in increasing `Fin r` order, on any test. -/
def simpleRootProductPoint (T : Over (Spec (CommRingCat.of k))) (c : Fin r → Γ(T.left, ⊤)) :
    T ⟶ G.X :=
  (List.ofFn fun j => (x (f j)).point T (c j) * (toUnit T ≫ (n (f j)).point)).prod

/-- The published Steinberg product is the ordered product along its ordering. -/
theorem steinbergProductPoint_eq (e : Fin r ≃ p.base.support)
    (T : Over (Spec (CommRingCat.of k))) (c : Fin r → Γ(T.left, ⊤)) :
    steinbergProductPoint e x n T c = simpleRootProductPoint e x n T c :=
  rfl

/-- The ordered product commutes with arbitrary precomposition. -/
theorem simpleRootProductPoint_comp {T W : Over (Spec (CommRingCat.of k))} (g : W ⟶ T)
    (c : Fin r → Γ(T.left, ⊤)) :
    g ≫ simpleRootProductPoint f x n T c =
      simpleRootProductPoint f x n W (fun j => g.left.appTop (c j)) := by
  have hg : g ≫ toUnit T = toUnit W := toUnit_unique _ _
  simp only [simpleRootProductPoint, comp_list_prod, List.map_ofFn, Function.comp_def,
    MonObj.comp_mul, NormalizedRootParametrization.point_comp, ← Category.assoc, hg]

/-- The empty ordered product is the identity point. -/
@[simp]
theorem simpleRootProductPoint_zero (f : Fin 0 → p.base.support)
    (T : Over (Spec (CommRingCat.of k))) (c : Fin 0 → Γ(T.left, ⊤)) :
    simpleRootProductPoint f x n T c = 1 := by
  simp [simpleRootProductPoint]

end OrderedProduct

variable (p) in
/-- Supplied data for Steinberg's modified cross-sections: two distinct simple roots `a`
and `b`, a root `α` with `α = a + b`, an actual parametrization of the whole root subgroup
of `α`, an actual reflection representative for `α`, and two nonzero scalars. No existence
of these data is asserted. -/
structure SteinbergModifiedData where
  a : p.base.support
  b : p.base.support
  a_ne_b : a ≠ b
  alpha : p.rootIndex
  root_eq : p.rootDatum.root alpha = p.rootDatum.root a + p.rootDatum.root b
  xAlpha : p.RootParametrization alpha
  nAlpha : p.ReflectionRepresentative alpha
  ca : k
  cb : k
  ca_ne_zero : ca ≠ 0
  cb_ne_zero : cb ≠ 0

namespace SteinbergModifiedData

variable (D : p.SteinbergModifiedData) (x : p.NormalizedSimpleRootParametrizations)

/-- The simple roots different from both `a` and `b`. -/
abbrev Complement : Type u := {j : p.base.support // j ≠ D.a ∧ j ≠ D.b}

/-- The rational point `u_a = x_a(c_a)`. -/
def ua : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X :=
  (x D.a).toRootParametrization.rationalPoint D.ca

/-- The rational point `u_b = x_b(c_b)`. -/
def ub : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X :=
  (x D.b).toRootParametrization.rationalPoint D.cb

theorem ua_ne_one : D.ua x ≠ 1 :=
  (x D.a).toRootParametrization.rationalPoint_ne_one D.ca_ne_zero

theorem ub_ne_one : D.ub x ≠ 1 :=
  (x D.b).toRootParametrization.rationalPoint_ne_one D.cb_ne_zero

theorem toUnit_comp_ua (T : Over (Spec (CommRingCat.of k))) :
    toUnit T ≫ D.ua x =
      (x D.a).point T (T.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv D.ca)) :=
  (x D.a).toRootParametrization.toUnit_comp_rationalPoint T D.ca

theorem toUnit_comp_ub (T : Over (Spec (CommRingCat.of k))) :
    toUnit T ≫ D.ub x =
      (x D.b).point T (T.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv D.cb)) :=
  (x D.b).toRootParametrization.toUnit_comp_rationalPoint T D.cb

end SteinbergModifiedData

variable (D : p.SteinbergModifiedData) {q : ℕ} (e : Fin q ≃ D.Complement)
    (x : p.NormalizedSimpleRootParametrizations)
    (n : p.SimpleReflectionRepresentatives)

/-- The formula `x_α(s) n_α ∏_j (x_(e j)(d_j) n_(e j))` on any test. -/
def steinbergModifiedProductPoint (T : Over (Spec (CommRingCat.of k))) (s : Γ(T.left, ⊤))
    (d : Fin q → Γ(T.left, ⊤)) : T ⟶ G.X :=
  D.xAlpha.point T s * (toUnit T ≫ D.nAlpha.point) *
    simpleRootProductPoint (fun j => (e j).1) x n T d

/-- The formula `u_b u_a x_α(s) n_α α^∨(t) ∏_j (x_(e j)(d_j) n_(e j))` on any test. -/
def steinbergModifiedTorusProductPoint (T : Over (Spec (CommRingCat.of k)))
    (t : T ⟶ (Gm (Spec (CommRingCat.of k))).X) (s : Γ(T.left, ⊤))
    (d : Fin q → Γ(T.left, ⊤)) : T ⟶ G.X :=
  (toUnit T ≫ D.ub x) * (toUnit T ≫ D.ua x) * D.xAlpha.point T s *
      (toUnit T ≫ D.nAlpha.point) * (t ≫ (p.corootHom D.alpha).hom.hom) *
    simpleRootProductPoint (fun j => (e j).1) x n T d

/-- The first formula commutes with arbitrary precomposition. -/
theorem steinbergModifiedProductPoint_comp {T W : Over (Spec (CommRingCat.of k))}
    (f : W ⟶ T) (s : Γ(T.left, ⊤)) (d : Fin q → Γ(T.left, ⊤)) :
    f ≫ steinbergModifiedProductPoint D e x n T s d =
      steinbergModifiedProductPoint D e x n W (f.left.appTop s)
        (fun j => f.left.appTop (d j)) := by
  have hf : f ≫ toUnit T = toUnit W := toUnit_unique _ _
  simp only [steinbergModifiedProductPoint, MonObj.comp_mul, RootParametrization.point_comp,
    simpleRootProductPoint_comp, ← Category.assoc, hf]

/-- The second formula commutes with arbitrary precomposition, pulling back the `𝔾_m`
point as well as the global functions. -/
theorem steinbergModifiedTorusProductPoint_comp {T W : Over (Spec (CommRingCat.of k))}
    (f : W ⟶ T) (t : T ⟶ (Gm (Spec (CommRingCat.of k))).X) (s : Γ(T.left, ⊤))
    (d : Fin q → Γ(T.left, ⊤)) :
    f ≫ steinbergModifiedTorusProductPoint D e x n T t s d =
      steinbergModifiedTorusProductPoint D e x n W (f ≫ t) (f.left.appTop s)
        (fun j => f.left.appTop (d j)) := by
  have hf : f ≫ toUnit T = toUnit W := toUnit_unique _ _
  simp only [steinbergModifiedTorusProductPoint, MonObj.comp_mul,
    RootParametrization.point_comp, simpleRootProductPoint_comp, ← Category.assoc, hf]

/-- Steinberg's modified ordered morphism `N''` from standard affine `(q+1)`-space. The
first coordinate is `s` and the remaining coordinates are the `d_j`. -/
def steinbergModifiedProduct :
    (VectorGroup.groupScheme (CommRingCat.of k) (q + 1)).X ⟶ G.X :=
  steinbergModifiedProductPoint D e x n _
    (VectorGroup.coordinateSection (CommRingCat.of k) (q + 1) 0)
    (fun j => VectorGroup.coordinateSection (CommRingCat.of k) (q + 1) j.succ)

/-- Steinberg's modified ordered morphism `N'''` from `𝔾_m × 𝔸^(q+1)`. -/
def steinbergModifiedTorusProduct :
    (Gm (Spec (CommRingCat.of k))).X ⊗ (VectorGroup.groupScheme (CommRingCat.of k) (q + 1)).X ⟶
      G.X :=
  steinbergModifiedTorusProductPoint D e x n _ (fst _ _)
    ((VectorGroup.coordinates (CommRingCat.of k) (q + 1) _ (snd _ _)).toAdd 0)
    (fun j => (VectorGroup.coordinates (CommRingCat.of k) (q + 1) _ (snd _ _)).toAdd j.succ)

/-- All-test formula for `N''`. -/
theorem comp_steinbergModifiedProduct {T : Over (Spec (CommRingCat.of k))}
    (c : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) (q + 1)).X) :
    c ≫ steinbergModifiedProduct D e x n =
      D.xAlpha.point T ((VectorGroup.coordinates (CommRingCat.of k) (q + 1) T c).toAdd 0) *
          (toUnit T ≫ D.nAlpha.point) *
        (List.ofFn fun j =>
          (x (e j).1).point T
              ((VectorGroup.coordinates (CommRingCat.of k) (q + 1) T c).toAdd j.succ) *
            (toUnit T ≫ (n (e j).1).point)).prod := by
  rw [steinbergModifiedProduct, steinbergModifiedProductPoint_comp]
  simp only [steinbergModifiedProductPoint, simpleRootProductPoint,
    VectorGroup.coordinates_apply]

/-- All-test formula for `N'''`, at the point with `𝔾_m` component `t` and affine
component `c`. -/
theorem lift_comp_steinbergModifiedTorusProduct {T : Over (Spec (CommRingCat.of k))}
    (t : T ⟶ (Gm (Spec (CommRingCat.of k))).X)
    (c : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) (q + 1)).X) :
    lift t c ≫ steinbergModifiedTorusProduct D e x n =
      (toUnit T ≫ D.ub x) * (toUnit T ≫ D.ua x) *
            D.xAlpha.point T ((VectorGroup.coordinates (CommRingCat.of k) (q + 1) T c).toAdd 0) *
          (toUnit T ≫ D.nAlpha.point) *
        (t ≫ (CommGroupScheme.groupHom (p.rootDatum.coroot D.alpha)).hom.hom ≫
          p.inclusion.hom.hom) *
        (List.ofFn fun j =>
          (x (e j).1).point T
              ((VectorGroup.coordinates (CommRingCat.of k) (q + 1) T c).toAdd j.succ) *
            (toUnit T ≫ (n (e j).1).point)).prod := by
  have hc : ∀ j, (lift t c).left.appTop
      ((VectorGroup.coordinates (CommRingCat.of k) (q + 1) _ (snd _ _)).toAdd j) =
        (VectorGroup.coordinates (CommRingCat.of k) (q + 1) T c).toAdd j := by
    intro j
    have h := congrFun (VectorGroup.coordinates_comp (lift t c) (snd _ _)) j
    rw [lift_snd] at h
    exact h.symm
  rw [steinbergModifiedTorusProduct, steinbergModifiedTorusProductPoint_comp, lift_fst]
  simp only [steinbergModifiedTorusProductPoint, simpleRootProductPoint, hc,
    corootHom_hom_hom]

/-- All-test formula for `N'''` at an arbitrary point of its domain. -/
theorem comp_steinbergModifiedTorusProduct {T : Over (Spec (CommRingCat.of k))}
    (g : T ⟶ (Gm (Spec (CommRingCat.of k))).X ⊗
      (VectorGroup.groupScheme (CommRingCat.of k) (q + 1)).X) :
    g ≫ steinbergModifiedTorusProduct D e x n =
      steinbergModifiedTorusProductPoint D e x n T (g ≫ fst _ _)
        ((VectorGroup.coordinates (CommRingCat.of k) (q + 1) T (g ≫ snd _ _)).toAdd 0)
        (fun j =>
          (VectorGroup.coordinates (CommRingCat.of k) (q + 1) T (g ≫ snd _ _)).toAdd j.succ) := by
  rw [steinbergModifiedTorusProduct, steinbergModifiedTorusProductPoint_comp,
    VectorGroup.coordinates_comp]

/-- `N''` evaluated at specified global functions `s` and `d_j`. -/
theorem coordinatesPoint_comp_steinbergModifiedProduct (T : Over (Spec (CommRingCat.of k)))
    (s : Γ(T.left, ⊤)) (d : Fin q → Γ(T.left, ⊤)) :
    (VectorGroup.coordinates (CommRingCat.of k) (q + 1) T).symm
          (Multiplicative.ofAdd (Fin.cons s d)) ≫ steinbergModifiedProduct D e x n =
      steinbergModifiedProductPoint D e x n T s d := by
  rw [comp_steinbergModifiedProduct]
  simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd, Fin.cons_zero, Fin.cons_succ,
    steinbergModifiedProductPoint, simpleRootProductPoint]

/-- `N'''` evaluated at a specified `𝔾_m` point `t` and global functions `s` and `d_j`. -/
theorem coordinatesPoint_comp_steinbergModifiedTorusProduct
    (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ (Gm (Spec (CommRingCat.of k))).X)
    (s : Γ(T.left, ⊤)) (d : Fin q → Γ(T.left, ⊤)) :
    lift t ((VectorGroup.coordinates (CommRingCat.of k) (q + 1) T).symm
          (Multiplicative.ofAdd (Fin.cons s d))) ≫ steinbergModifiedTorusProduct D e x n =
      steinbergModifiedTorusProductPoint D e x n T t s d := by
  rw [lift_comp_steinbergModifiedTorusProduct]
  simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd, Fin.cons_zero, Fin.cons_succ,
    steinbergModifiedTorusProductPoint, simpleRootProductPoint, corootHom_hom_hom]

section Empty

variable (e₀ : Fin 0 ≃ D.Complement)

/-- With empty complement, the first formula is `x_α(s) n_α`. -/
@[simp]
theorem steinbergModifiedProductPoint_zero (T : Over (Spec (CommRingCat.of k)))
    (s : Γ(T.left, ⊤)) (d : Fin 0 → Γ(T.left, ⊤)) :
    steinbergModifiedProductPoint D e₀ x n T s d =
      D.xAlpha.point T s * (toUnit T ≫ D.nAlpha.point) := by
  rw [steinbergModifiedProductPoint, simpleRootProductPoint_zero, mul_one]

/-- With empty complement, the second formula is `u_b u_a x_α(s) n_α α^∨(t)`. -/
@[simp]
theorem steinbergModifiedTorusProductPoint_zero (T : Over (Spec (CommRingCat.of k)))
    (t : T ⟶ (Gm (Spec (CommRingCat.of k))).X) (s : Γ(T.left, ⊤))
    (d : Fin 0 → Γ(T.left, ⊤)) :
    steinbergModifiedTorusProductPoint D e₀ x n T t s d =
      (toUnit T ≫ D.ub x) * (toUnit T ≫ D.ua x) * D.xAlpha.point T s *
        (toUnit T ≫ D.nAlpha.point) * (t ≫ (p.corootHom D.alpha).hom.hom) := by
  rw [steinbergModifiedTorusProductPoint, simpleRootProductPoint_zero, mul_one]

/-- With empty complement, `N''` is `x_α(s) n_α` on every test. -/
theorem comp_steinbergModifiedProduct_zero {T : Over (Spec (CommRingCat.of k))}
    (c : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) (0 + 1)).X) :
    c ≫ steinbergModifiedProduct D e₀ x n =
      D.xAlpha.point T ((VectorGroup.coordinates (CommRingCat.of k) (0 + 1) T c).toAdd 0) *
        (toUnit T ≫ D.nAlpha.point) := by
  rw [steinbergModifiedProduct, steinbergModifiedProductPoint_comp,
    steinbergModifiedProductPoint_zero, VectorGroup.coordinates_apply]

/-- With empty complement, `N'''` is `u_b u_a x_α(s) n_α α^∨(t)` on every test. -/
theorem lift_comp_steinbergModifiedTorusProduct_zero {T : Over (Spec (CommRingCat.of k))}
    (t : T ⟶ (Gm (Spec (CommRingCat.of k))).X)
    (c : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) (0 + 1)).X) :
    lift t c ≫ steinbergModifiedTorusProduct D e₀ x n =
      (toUnit T ≫ D.ub x) * (toUnit T ≫ D.ua x) *
          D.xAlpha.point T ((VectorGroup.coordinates (CommRingCat.of k) (0 + 1) T c).toAdd 0) *
        (toUnit T ≫ D.nAlpha.point) *
        (t ≫ (CommGroupScheme.groupHom (p.rootDatum.coroot D.alpha)).hom.hom ≫
          p.inclusion.hom.hom) := by
  rw [lift_comp_steinbergModifiedTorusProduct]
  simp

end Empty

end SplitPinning

end Langlands.GroupScheme
