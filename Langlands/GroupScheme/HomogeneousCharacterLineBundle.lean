import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
import Langlands.GroupScheme.Rational.Characters
import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescentEffectiveProof

/-! # Character line bundles on actual homogeneous quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

variable {S : Scheme.{u}} {G H : GroupScheme S} (i : H ⟶ G)
  (D : HomogeneousQuotient i)

/-- The subgroup point lifting the right difference of two equal-coset points. -/
def subgroupDifference {T : Over S} (a b : T ⟶ G.X)
    (h : a ≫ D.projection = b ≫ D.projection) : T ⟶ H.X :=
  Classical.choose (SubgroupFunctor.mem_range.mp ((D.fibers T a b).mp h))

@[simp] theorem subgroupDifference_comp {T : Over S} (a b : T ⟶ G.X)
    (h : a ≫ D.projection = b ≫ D.projection) :
    subgroupDifference i D a b h ≫ i.hom.hom = a⁻¹ * b :=
  Classical.choose_spec (SubgroupFunctor.mem_range.mp ((D.fibers T a b).mp h))

/-- The subgroup difference is natural on every relative test scheme. -/
theorem subgroupDifference_naturality [Mono i.hom.hom] {T T' : Over S} (f : T' ⟶ T)
    (a b : T ⟶ G.X) (h : a ≫ D.projection = b ≫ D.projection)
    (h' : (f ≫ a) ≫ D.projection = (f ≫ b) ≫ D.projection) :
    subgroupDifference i D (f ≫ a) (f ≫ b) h' = f ≫ subgroupDifference i D a b h := by
  apply (cancel_mono i.hom.hom).mp
  simp only [Category.assoc, subgroupDifference_comp, MonObj.comp_mul, GrpObj.comp_inv]

/-- Subgroup differences compose multiplicatively along three equal-coset points. -/
theorem subgroupDifference_mul [Mono i.hom.hom] {T : Over S} (a b d : T ⟶ G.X)
    (h : a ≫ D.projection = b ≫ D.projection)
    (h' : b ≫ D.projection = d ≫ D.projection)
    (h'' : a ≫ D.projection = d ≫ D.projection) :
    subgroupDifference i D a b h * subgroupDifference i D b d h' =
      subgroupDifference i D a d h'' := by
  apply (cancel_mono i.hom.hom).mp
  simp only [MonObj.mul_comp, subgroupDifference_comp]
  group

/-- Equal quotient composites give equal structure maps to the base. -/
lemma pair_base_eq {U : Scheme.{u}} {a b : U ⟶ G.X.left}
    (h : a ≫ D.projection.left = b ≫ D.projection.left) :
    a ≫ G.X.hom = b ≫ G.X.hom := by
  rw [← Over.w D.projection, ← Category.assoc, h, Category.assoc]

/-- The first point of a scheme-valued equal-coset pair, as a relative point. -/
def pairFirst {U : Scheme.{u}} (a : U ⟶ G.X.left) :
    Over.mk (a ≫ G.X.hom) ⟶ G.X := Over.homMk a

/-- The second point with the structure map determined by the first point. -/
def pairSecond {U : Scheme.{u}} (a b : U ⟶ G.X.left)
    (h : a ≫ D.projection.left = b ≫ D.projection.left) :
    Over.mk (a ≫ G.X.hom) ⟶ G.X :=
  Over.homMk b (pair_base_eq i D h).symm

lemma pair_comp_eq {U : Scheme.{u}} (a b : U ⟶ G.X.left)
    (h : a ≫ D.projection.left = b ≫ D.projection.left) :
    pairFirst a ≫ D.projection = pairSecond i D a b h ≫ D.projection :=
  Over.OverMorphism.ext h

/-- The actual character cocycle on all scheme-valued equal-coset pairs. -/
def characterCocycle (χ : rationalCharacters H) (U : Scheme.{u})
    (a b : U ⟶ G.X.left) (h : a ≫ D.projection.left = b ≫ D.projection.left) : Γ(U, ⊤)ˣ :=
  characterEval χ (Over.mk (a ≫ G.X.hom))
    (subgroupDifference i D (pairFirst a) (pairSecond i D a b h) (pair_comp_eq i D a b h))

/-- The scheme-valued cocycle agrees with evaluation of the actual relative difference. -/
theorem characterCocycle_on_over [Mono i.hom.hom] (χ : rationalCharacters H) (T : Over S)
    (a b : T ⟶ G.X) (h : a ≫ D.projection = b ≫ D.projection) :
    characterCocycle i D χ T.left a.left b.left (congrArg Over.Hom.left h) =
      characterEval χ T (subgroupDifference i D a b h) := by
  let f : Over.mk (a.left ≫ G.X.hom) ⟶ T :=
    Over.homMk (𝟙 T.left) (by simp)
  have ha : pairFirst a.left = f ≫ a := by ext; simp [pairFirst, f]
  have hb : pairSecond i D a.left b.left (congrArg Over.Hom.left h) = f ≫ b := by
    ext; simp [pairSecond, f]
  have h' : (f ≫ a) ≫ D.projection = (f ≫ b) ≫ D.projection := by
    simpa only [Category.assoc] using congrArg (fun t => f ≫ t) h
  have hd : subgroupDifference i D (pairFirst a.left)
      (pairSecond i D a.left b.left (congrArg Over.Hom.left h))
      (pair_comp_eq i D a.left b.left (congrArg Over.Hom.left h)) =
      subgroupDifference i D (f ≫ a) (f ≫ b) h' := by
    apply (cancel_mono i.hom.hom).mp
    simp only [subgroupDifference_comp, ha, hb]
  unfold characterCocycle
  rw [hd, subgroupDifference_naturality i D f a b h h', characterEval_naturality]
  simp [f]

/-- The character cocycle is natural under arbitrary scheme precomposition. -/
theorem characterCocycle_isNatural [Mono i.hom.hom] (χ : rationalCharacters H) :
    Langlands.Scheme.UnitCocycleDescent.IsNatural D.projection.left (characterCocycle i D χ) := by
  intro U V f a b h h'
  let T := Over.mk (a ≫ G.X.hom)
  let T' := Over.mk (f ≫ T.hom)
  let g : T' ⟶ T := Over.homMk f
  let x : T ⟶ G.X := pairFirst a
  let y : T ⟶ G.X := pairSecond i D a b h
  have hxy : x ≫ D.projection = y ≫ D.projection := pair_comp_eq i D a b h
  have hxy' : (g ≫ x) ≫ D.projection = (g ≫ y) ≫ D.projection := by
    simpa only [Category.assoc] using congrArg (fun t => g ≫ t) hxy
  change characterCocycle i D χ T'.left (g ≫ x).left (g ≫ y).left
      (congrArg Over.Hom.left hxy') =
    Units.map g.left.appTop.hom.toMonoidHom
      (characterCocycle i D χ T.left x.left y.left (congrArg Over.Hom.left hxy))
  rw [characterCocycle_on_over i D χ T' (g ≫ x) (g ≫ y) hxy',
    characterCocycle_on_over i D χ T x y hxy,
    subgroupDifference_naturality i D g x y hxy hxy', characterEval_naturality]

/-- The character cocycle satisfies the multiplicative triple identity. -/
theorem characterCocycle_isMultiplicative [Mono i.hom.hom] (χ : rationalCharacters H) :
    Langlands.Scheme.UnitCocycleDescent.IsMultiplicative D.projection.left
      (characterCocycle i D χ) := by
  intro U a b d h h' h''
  let T := Over.mk (a ≫ G.X.hom)
  let x : T ⟶ G.X := pairFirst a
  let y : T ⟶ G.X := pairSecond i D a b h
  let z : T ⟶ G.X := pairSecond i D a d h''
  have hxy : x ≫ D.projection = y ≫ D.projection := pair_comp_eq i D a b h
  have hyz : y ≫ D.projection = z ≫ D.projection := Over.OverMorphism.ext h'
  have hxz : x ≫ D.projection = z ≫ D.projection := pair_comp_eq i D a d h''
  change characterCocycle i D χ T.left x.left y.left (congrArg Over.Hom.left hxy) *
      characterCocycle i D χ T.left y.left z.left (congrArg Over.Hom.left hyz) =
    characterCocycle i D χ T.left x.left z.left (congrArg Over.Hom.left hxz)
  rw [characterCocycle_on_over i D χ T x y hxy,
    characterCocycle_on_over i D χ T y z hyz,
    characterCocycle_on_over i D χ T x z hxz,
    ← map_mul, subgroupDifference_mul i D x y z hxy hyz hxz]

/-- Affineness of the source over the base and separatedness of the quotient
already force the quotient projection to be affine. -/
theorem isAffineHom_projection [IsAffineHom G.X.hom] : IsAffineHom D.projection.left := by
  let : IsSeparated D.scheme.hom := D.separated
  have : IsAffineHom (D.projection.left ≫ D.scheme.hom) := by
    rw [Over.w D.projection]
    infer_instance
  exact IsAffineHom.of_comp D.projection.left D.scheme.hom

open Langlands.Scheme.UnitCocycleDescent Langlands.AlgebraicGeometry.Picard

/-- The line bundle obtained by effective descent of the actual character cocycle. -/
def characterLineBundle [Mono i.hom.hom] [IsAffineHom G.X.hom]
    (χ : rationalCharacters H) : LineBundle D.scheme.left where
  obj := cocycleModule D.projection.left (characterCocycle i D χ)
  property := by
    let := isAffineHom_projection i D
    let := D.smooth_projection
    let := D.surjective_projection
    exact isLocallyFreeRankOne_cocycleModule Langlands.Algebra.unitCocycleLocalUnits
      (characterCocycle_isNatural i D χ) (characterCocycle_isMultiplicative i D χ)

/-- The character line bundle has its actual descent trivialization on the group. -/
def characterLineBundleTrivialization [Mono i.hom.hom] [IsAffineHom G.X.hom]
    (χ : rationalCharacters H) :
    (Scheme.Modules.pullback D.projection.left).obj (characterLineBundle i D χ).obj ≅
      SheafOfModules.unit G.X.left.ringCatSheaf := by
  letI := isAffineHom_projection i D
  letI := D.smooth_projection
  letI := D.surjective_projection
  exact @asIso _ _ _ _ (cocycleTriv D.projection.left (characterCocycle i D χ))
    (isIso_cocycleTriv Langlands.Algebra.unitCocycleLocalUnits
      (characterCocycle_isNatural i D χ) (characterCocycle_isMultiplicative i D χ))

/-- The all-test right-character covariance equation for a regular function. -/
def IsRightCharacterCovariant (χ : rationalCharacters H) (f : Γ(G.X.left, ⊤)) : Prop :=
  ∀ (T : Over S) (a : T ⟶ G.X) (b : T ⟶ H.X),
    (a * (b ≫ i.hom.hom)).left.appTop f =
      (characterEval χ T b).1 * a.left.appTop f

/-- Multiplication on the right by a subgroup point preserves the quotient point. -/
theorem projection_mul_subgroup {T : Over S} (a : T ⟶ G.X) (b : T ⟶ H.X) :
    a ≫ D.projection = (a * (b ≫ i.hom.hom)) ≫ D.projection := by
  apply (D.fibers T _ _).mpr
  apply SubgroupFunctor.mem_range.mpr
  exact ⟨b, by group⟩

/-- The difference between a point and its translate is the translating subgroup point. -/
theorem subgroupDifference_mul_subgroup [Mono i.hom.hom] {T : Over S}
    (a : T ⟶ G.X) (b : T ⟶ H.X) :
    subgroupDifference i D a (a * (b ≫ i.hom.hom))
      (projection_mul_subgroup i D a b) = b := by
  apply (cancel_mono i.hom.hom).mp
  rw [subgroupDifference_comp]
  group

/-- A top cocycle section is precisely an all-test right-character-covariant function. -/
theorem isCocycleSection_top_iff [Mono i.hom.hom] (χ : rationalCharacters H)
    (f : Γ(G.X.left, ⊤)) :
    IsCocycleSection D.projection.left (characterCocycle i D χ) ⊤ f ↔
      IsRightCharacterCovariant i χ f := by
  constructor
  · intro hf T a b
    have h := projection_mul_subgroup i D a b
    have h' := congrArg Over.Hom.left h
    have key := hf T.left a.left (a * (b ≫ i.hom.hom)).left h' ⊤
      (by simp) (by simp)
    rw [characterCocycle_on_over i D χ T a (a * (b ≫ i.hom.hom)) h,
      subgroupDifference_mul_subgroup] at key
    simpa [Scheme.Hom.preimage_top, ← appTop_eq_appLE] using key.symm
  · intro hf
    apply IsCocycleSection.of_top (characterCocycle_isNatural i D χ)
    intro U a b h ha hb
    let T := Over.mk (a ≫ G.X.hom)
    let x : T ⟶ G.X := pairFirst a
    let y : T ⟶ G.X := pairSecond i D a b h
    have hxy : x ≫ D.projection = y ≫ D.projection := pair_comp_eq i D a b h
    let d := subgroupDifference i D x y hxy
    have hmul : x * (d ≫ i.hom.hom) = y := by
      dsimp only [d]
      rw [subgroupDifference_comp]
      group
    have key := hf T x d
    rw [hmul] at key
    have hc := characterCocycle_on_over i D χ T x y hxy
    change characterCocycle i D χ U a b h = characterEval χ T d at hc
    dsimp only [T, x, y, pairFirst, pairSecond] at key hc
    rw [hc]
    simpa only [Scheme.Hom.preimage_top, ← appTop_eq_appLE,
      Over.homMk_left, Over.mk_left] using key.symm

/-- The underlying regular function of a global section of the character line bundle. -/
def characterSectionFunction [Mono i.hom.hom] [IsAffineHom G.X.hom]
    (χ : rationalCharacters H) (s : (characterLineBundle i D χ).sections) : Γ(G.X.left, ⊤) :=
  s.1

/-- The entire module of right-character-covariant regular functions, with scalars
pulled back from the actual quotient. -/
def rightCharacterCovariantSubmodule [Mono i.hom.hom] (χ : rationalCharacters H) :
    Submodule Γ(D.scheme.left, ⊤) Γ(pushforwardUnit D.projection.left, ⊤) where
  carrier := {f | IsRightCharacterCovariant i χ f}
  zero_mem' := (isCocycleSection_top_iff i D χ 0).mp (IsCocycleSection.zero ⊤)
  add_mem' hf hg := (isCocycleSection_top_iff i D χ _).mp
    (((isCocycleSection_top_iff i D χ _).mpr hf).add
      ((isCocycleSection_top_iff i D χ _).mpr hg))
  smul_mem' r _ hf := (isCocycleSection_top_iff i D χ _).mp
    (((isCocycleSection_top_iff i D χ _).mpr hf).app_mul r)

/-- Global sections of the descended character line bundle identify linearly with
all right-character-covariant regular functions on the group. -/
def characterSectionsEquiv [Mono i.hom.hom] [IsAffineHom G.X.hom]
    (χ : rationalCharacters H) :
    (characterLineBundle i D χ).sections ≃ₗ[Γ(D.scheme.left, ⊤)]
      rightCharacterCovariantSubmodule i D χ where
  toFun s := ⟨s.1, (isCocycleSection_top_iff i D χ s.1).mp s.2⟩
  invFun f := ⟨f.1, (isCocycleSection_top_iff i D χ f.1).mpr f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem characterSectionsEquiv_apply [Mono i.hom.hom] [IsAffineHom G.X.hom]
    (χ : rationalCharacters H) (s : (characterLineBundle i D χ).sections) :
    (characterSectionsEquiv i D χ s).1 = characterSectionFunction i D χ s := rfl

end Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
