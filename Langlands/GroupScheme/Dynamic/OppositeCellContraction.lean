import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Dynamic.Decomposition

/-! # Splitting contractions through an injective product cell -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Evaluation of an affine-line morphism at the section with coordinate one. -/
def evalOne {T Y : Over S} (e : T ⊗ AffineLine.scheme S ⟶ Y) : T ⟶ Y :=
  lift (𝟙 T) ((1 : T ⟶ (Gm S).X) ≫ AffineLine.unitInclusion S) ≫ e

theorem evalOne_mul {T : Over S} (e e' : T ⊗ AffineLine.scheme S ⟶ G.X) :
    evalOne (e * e') = evalOne e * evalOne e' :=
  MonObj.comp_mul _ _ _

theorem evalOne_comp {T Y Y' : Over S} (e : T ⊗ AffineLine.scheme S ⟶ Y)
    (f : Y ⟶ Y') : evalOne (e ≫ f) = evalOne e ≫ f :=
  (Category.assoc _ _ _).symm

/-- At one, an orbit extension has its original value. -/
theorem IsOrbitExtension.evalOne (χ : (Gm S).toGrp ⟶ G) {T : Over S}
    {g : T ⟶ G.X} {e : T ⊗ AffineLine.scheme S ⟶ G.X}
    (he : IsOrbitExtension χ g e) : evalOne e = g := by
  rw [Dynamic.evalOne, ← lift_whiskerLeft_assoc, he]
  simp only [orbit, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc,
    lift_fst_assoc, MonObj.one_comp, Category.id_comp, one_mul, inv_one, mul_one]

/-- The contraction of `g` extends with both factors lying in the prescribed
subgroup functors on the entire affine line. -/
def HasProductContraction (χ : (Gm S).toGrp ⟶ G)
    (A B : SubgroupFunctor G) {T : Over S} (g : T ⟶ G.X) : Prop :=
  ∃ eA eB : T ⊗ AffineLine.scheme S ⟶ G.X,
    eA ∈ A.carrier (T ⊗ AffineLine.scheme S) ∧
    eB ∈ B.carrier (T ⊗ AffineLine.scheme S) ∧
    IsOrbitExtension χ g (eA * eB) ∧ evalZero (eA * eB) = 1

/-- Cocharacters factoring through the same commutative group centralize one
another on every test scheme. -/
theorem range_comp_le_centralizer_comp {C : CommGroupScheme S}
    (i : C.toGrp ⟶ G) (a b : (Gm S).toGrp ⟶ C.toGrp) :
    SubgroupFunctor.range (a ≫ i) ≤ centralizer (b ≫ i) := by
  intro T g hg
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  have hc := (Commute.all (snd T (Gm S).X ≫ b.hom.hom)
    (fst T (Gm S).X ≫ t ≫ a.hom.hom)).map
      (((yonedaGrp.map i).app (op (T ⊗ (Gm S).X))).hom)
  change Commute ((snd T (Gm S).X ≫ b.hom.hom) ≫ i.hom.hom)
    ((fst T (Gm S).X ≫ t ≫ a.hom.hom) ≫ i.hom.hom) at hc
  rw [mem_centralizer, orbit]
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  simp only [← Category.assoc] at hc
  rw [hc.eq, mul_inv_cancel_right]

/-- Cocharacters in a common commutative group normalize one another's
dynamic parabolics. -/
theorem parabolic_isNormalizedBy_range_of_common_commutativeGroup
    {C : CommGroupScheme S} (i : C.toGrp ⟶ G) (a b : (Gm S).toGrp ⟶ C.toGrp) :
    (parabolic (b ≫ i)).IsNormalizedBy (SubgroupFunctor.range (a ≫ i)) := by
  intro T x y hx hy
  have hxP := centralizer_le_parabolic (b ≫ i) T
    (range_comp_le_centralizer_comp i a b T hx)
  exact ((parabolic (b ≫ i)).carrier T).mul_mem
    (((parabolic (b ≫ i)).carrier T).mul_mem hxP hy)
    (((parabolic (b ≫ i)).carrier T).inv_mem hxP)

/-- Cocharacters in a common commutative group normalize one another's
dynamic unipotent subgroups. -/
theorem unipotent_isNormalizedBy_range_of_common_commutativeGroup
    {C : CommGroupScheme S} (i : C.toGrp ⟶ G) (a b : (Gm S).toGrp ⟶ C.toGrp) :
    (unipotent (b ≫ i)).IsNormalizedBy (SubgroupFunctor.range (a ≫ i)) := by
  intro T x y hx hy
  exact conj_mem_unipotent (b ≫ i)
    (centralizer_le_parabolic (b ≫ i) T (range_comp_le_centralizer_comp i a b T hx)) hy

variable (χ : (Gm S).toGrp ⟶ G) (A B : SubgroupFunctor G)
  (hA : A.IsNormalizedBy (SubgroupFunctor.range χ))
  (hB : B.IsNormalizedBy (SubgroupFunctor.range χ))
  (hinj : ∀ X : Over S, Function.Injective
    (fun z : A.carrier X × B.carrier X => (z.1 : X ⟶ G.X) * z.2))

include hA hB hinj in
/-- If a product extension is an orbit extension, injectivity of the product
forces each factor to be the corresponding orbit extension. -/
theorem IsOrbitExtension.factors {T : Over S} {a b : T ⟶ G.X}
    (ha : a ∈ A.carrier T) (hb : b ∈ B.carrier T)
    {eA eB : T ⊗ AffineLine.scheme S ⟶ G.X}
    (heA : eA ∈ A.carrier (T ⊗ AffineLine.scheme S))
    (heB : eB ∈ B.carrier (T ⊗ AffineLine.scheme S))
    (he : IsOrbitExtension χ (a * b) (eA * eB)) :
    IsOrbitExtension χ a eA ∧ IsOrbitExtension χ b eB := by
  let X := T ⊗ (Gm S).X
  have hoA : orbit χ a ∈ A.carrier X :=
    hA X _ _ (SubgroupFunctor.mem_range.mpr ⟨snd T (Gm S).X, rfl⟩)
      (A.comp_mem (fst T (Gm S).X) ha)
  have hoB : orbit χ b ∈ B.carrier X :=
    hB X _ _ (SubgroupFunctor.mem_range.mpr ⟨snd T (Gm S).X, rfl⟩)
      (B.comp_mem (fst T (Gm S).X) hb)
  have hrA : T ◁ AffineLine.unitInclusion S ≫ eA ∈ A.carrier X :=
    A.comp_mem (T ◁ AffineLine.unitInclusion S) heA
  have hrB : T ◁ AffineLine.unitInclusion S ≫ eB ∈ B.carrier X :=
    B.comp_mem (T ◁ AffineLine.unitInclusion S) heB
  let x : A.carrier X × B.carrier X := (⟨_, hrA⟩, ⟨_, hrB⟩)
  let y : A.carrier X × B.carrier X := (⟨_, hoA⟩, ⟨_, hoB⟩)
  have hprod : (x.1 : X ⟶ G.X) * x.2 = (y.1 : X ⟶ G.X) * y.2 := by
    simpa only [IsOrbitExtension, MonObj.comp_mul, orbit_mul] using he
  have hxy : x = y := hinj X hprod
  exact ⟨congrArg (fun z : A.carrier X × B.carrier X => (z.1 : X ⟶ G.X)) hxy,
    congrArg (fun z : A.carrier X × B.carrier X => (z.2 : X ⟶ G.X)) hxy⟩

include hinj in
/-- An identity-valued product at zero has identity-valued factors when their
subgroup multiplication is injective. -/
theorem evalZero_factors_eq_one {T : Over S}
    {eA eB : T ⊗ AffineLine.scheme S ⟶ G.X}
    (heA : eA ∈ A.carrier (T ⊗ AffineLine.scheme S))
    (heB : eB ∈ B.carrier (T ⊗ AffineLine.scheme S))
    (h0 : evalZero (eA * eB) = 1) :
    evalZero eA = 1 ∧ evalZero eB = 1 := by
  have hzA : evalZero eA ∈ A.carrier T :=
    A.comp_mem (lift (𝟙 T) (toUnit T ≫ AffineLine.zeroSection S)) heA
  have hzB : evalZero eB ∈ B.carrier T :=
    B.comp_mem (lift (𝟙 T) (toUnit T ≫ AffineLine.zeroSection S)) heB
  let x : A.carrier T × B.carrier T := (⟨_, hzA⟩, ⟨_, hzB⟩)
  let y : A.carrier T × B.carrier T :=
    (⟨1, (A.carrier T).one_mem⟩, ⟨1, (B.carrier T).one_mem⟩)
  have hprod : (x.1 : T ⟶ G.X) * x.2 = (y.1 : T ⟶ G.X) * y.2 := by
    change evalZero eA * evalZero eB = 1 * 1
    simpa only [evalZero_mul, one_mul] using h0
  have hxy : x = y := hinj T hprod
  exact ⟨congrArg (fun z : A.carrier T × B.carrier T => (z.1 : T ⟶ G.X)) hxy,
    congrArg (fun z : A.carrier T × B.carrier T => (z.2 : T ⟶ G.X)) hxy⟩

include hA hB hinj in
/-- A contraction through an injective normalized product splits into
contractions of both factors. -/
theorem HasProductContraction.exists_unipotent_factors {T : Over S} {g : T ⟶ G.X}
    (hg : HasProductContraction χ A B g) :
    ∃ a b : T ⟶ G.X, a ∈ A.carrier T ∧ b ∈ B.carrier T ∧
      a ∈ (unipotent χ).carrier T ∧ b ∈ (unipotent χ).carrier T ∧ g = a * b := by
  obtain ⟨eA, eB, heA, heB, he, h0⟩ := hg
  let a := evalOne eA
  let b := evalOne eB
  have ha : a ∈ A.carrier T := A.comp_mem _ heA
  have hb : b ∈ B.carrier T := B.comp_mem _ heB
  have hab : g = a * b := by
    rw [← he.evalOne χ, evalOne_mul]
  have he' : IsOrbitExtension χ (a * b) (eA * eB) := by
    rw [← hab]
    exact he
  have hf := he'.factors χ A B hA hB hinj ha hb heA heB
  have hz := evalZero_factors_eq_one A B hinj heA heB h0
  exact ⟨a, b, ha, hb, ⟨eA, hf.1, hz.1⟩, ⟨eB, hf.2, hz.2⟩, hab⟩

/-- A lift of a contraction through represented subgroup multiplication gives
an extension whose two factors lie in those subgroup functors everywhere. -/
theorem hasProductContraction_of_represented_lift
    {H K : GroupScheme S} {iH : H ⟶ G} {iK : K ⟶ G}
    (hH : A.IsRepresentedBy iH) (hK : B.IsRepresentedBy iK)
    {T : Over S} {g : T ⟶ G.X} {e : T ⊗ AffineLine.scheme S ⟶ G.X}
    (he : IsOrbitExtension χ g e) (he0 : evalZero e = 1)
    (q : T ⊗ AffineLine.scheme S ⟶ H.X ⊗ K.X)
    (hq : q ≫ ((fst H.X K.X ≫ iH.hom.hom) *
      (snd H.X K.X ≫ iK.hom.hom)) = e) :
    HasProductContraction χ A B g := by
  let eA := q ≫ fst H.X K.X ≫ iH.hom.hom
  let eB := q ≫ snd H.X K.X ≫ iK.hom.hom
  have heA : eA ∈ A.carrier (T ⊗ AffineLine.scheme S) := by
    rw [← hH.2]
    exact SubgroupFunctor.mem_range.mpr ⟨q ≫ fst H.X K.X, rfl⟩
  have heB : eB ∈ B.carrier (T ⊗ AffineLine.scheme S) := by
    rw [← hK.2]
    exact SubgroupFunctor.mem_range.mpr ⟨q ≫ snd H.X K.X, rfl⟩
  have hprod : eA * eB = e := by
    simpa only [MonObj.comp_mul] using hq
  exact ⟨eA, eB, heA, heB, hprod.symm ▸ he, hprod.symm ▸ he0⟩

end Langlands.GroupScheme.Dynamic
