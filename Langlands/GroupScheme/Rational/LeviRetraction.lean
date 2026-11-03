import Langlands.GroupScheme.Rational.LeviSubgroup

/-! # The retraction supplied by an actual Levi multiplication isomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {S : Scheme.{u}} {L U P : GroupScheme S}
  (l : L ⟶ P) (r : U ⟶ P) [IsIso (subgroupMultiplication l r)]

/-- The Levi coordinate of a point, obtained from the inverse of the actual
multiplication isomorphism. -/
def leviComponent {T : Over S} (x : T ⟶ P.X) : T ⟶ L.X :=
  x ≫ inv (subgroupMultiplication l r) ≫ fst L.X U.X

/-- The radical coordinate of a point, obtained from the same inverse. -/
def radicalComponent {T : Over S} (x : T ⟶ P.X) : T ⟶ U.X :=
  x ≫ inv (subgroupMultiplication l r) ≫ snd L.X U.X

@[simp] theorem leviComponent_product {T : Over S} (a : T ⟶ L.X) (n : T ⟶ U.X) :
    leviComponent l r ((a ≫ l.hom.hom) * (n ≫ r.hom.hom)) = a := by
  rw [← comp_subgroupMultiplication]
  simp [leviComponent]

@[simp] theorem radicalComponent_product {T : Over S} (a : T ⟶ L.X) (n : T ⟶ U.X) :
    radicalComponent l r ((a ≫ l.hom.hom) * (n ≫ r.hom.hom)) = n := by
  rw [← comp_subgroupMultiplication]
  simp [radicalComponent]

/-- Every point has its exact Levi-times-radical decomposition on its original
test scheme. -/
theorem leviComponent_mul_radicalComponent {T : Over S} (x : T ⟶ P.X) :
    (leviComponent l r x ≫ l.hom.hom) * (radicalComponent l r x ≫ r.hom.hom) = x := by
  rw [← comp_subgroupMultiplication]
  simp only [leviComponent, radicalComponent]
  rw [← comp_lift, ← comp_lift, lift_fst_snd]
  simp

@[simp] theorem leviComponent_comp {T V : Over S} (a : V ⟶ T) (x : T ⟶ P.X) :
    leviComponent l r (a ≫ x) = a ≫ leviComponent l r x := by
  simp only [leviComponent, Category.assoc]

@[simp] theorem radicalComponent_comp {T V : Over S} (a : V ⟶ T) (x : T ⟶ P.X) :
    radicalComponent l r (a ≫ x) = a ≫ radicalComponent l r x := by
  simp only [radicalComponent, Category.assoc]

@[simp] theorem leviComponent_one (T : Over S) :
    leviComponent l r (1 : T ⟶ P.X) = 1 := by
  simpa only [MonObj.one_comp, one_mul] using
    leviComponent_product l r (1 : T ⟶ L.X) (1 : T ⟶ U.X)

@[simp] theorem leviComponent_comp_levi {T : Over S} (a : T ⟶ L.X) :
    leviComponent l r (a ≫ l.hom.hom) = a := by
  simpa only [MonObj.one_comp, mul_one] using
    leviComponent_product l r a (1 : T ⟶ U.X)

@[simp] theorem leviComponent_comp_radical {T : Over S} (n : T ⟶ U.X) :
    leviComponent l r (n ≫ r.hom.hom) = 1 := by
  simpa only [MonObj.one_comp, one_mul] using
    leviComponent_product l r (1 : T ⟶ L.X) n

/-- Normality of the radical makes the first coordinate multiplicative. -/
theorem leviComponent_mul (hn : (SubgroupFunctor.range r).IsNormal)
    {T : Over S} (x y : T ⟶ P.X) :
    leviComponent l r (x * y) = leviComponent l r x * leviComponent l r y := by
  let a := leviComponent l r x
  let b := leviComponent l r y
  let n := radicalComponent l r x
  let m := radicalComponent l r y
  have hnx : n ≫ r.hom.hom ∈ (SubgroupFunctor.range r).carrier T := ⟨n, rfl⟩
  have hwmem := hn T (b ≫ l.hom.hom)⁻¹ (n ≫ r.hom.hom)
    (Subgroup.mem_top _) hnx
  change ∃ w : T ⟶ U.X, w ≫ r.hom.hom =
    (b ≫ l.hom.hom)⁻¹ * (n ≫ r.hom.hom) * ((b ≫ l.hom.hom)⁻¹)⁻¹ at hwmem
  obtain ⟨w, hw⟩ := hwmem
  have hxy :
      ((a * b) ≫ l.hom.hom) * ((w * m) ≫ r.hom.hom) = x * y := by
    rw [MonObj.mul_comp, MonObj.mul_comp, hw]
    simp only [inv_inv]
    calc
      ((a ≫ l.hom.hom) * (b ≫ l.hom.hom)) *
          (((b ≫ l.hom.hom)⁻¹ * (n ≫ r.hom.hom) * (b ≫ l.hom.hom)) *
            (m ≫ r.hom.hom)) =
          ((a ≫ l.hom.hom) * (n ≫ r.hom.hom)) *
            ((b ≫ l.hom.hom) * (m ≫ r.hom.hom)) := by group
      _ = x * y := by
        rw [leviComponent_mul_radicalComponent, leviComponent_mul_radicalComponent]
  rw [← hxy, leviComponent_product]

/-- The natural homomorphism on points that forgets the radical coordinate. -/
def leviRetractionPoints (hn : (SubgroupFunctor.range r).IsNormal) (T : Over S) :
    (T ⟶ P.X) →* (T ⟶ L.X) where
  toFun := leviComponent l r
  map_one' := leviComponent_one l r T
  map_mul' := leviComponent_mul l r hn

/-- An actual group-scheme retraction onto the Levi factor. -/
def leviRetraction (hn : (SubgroupFunctor.range r).IsNormal) : P ⟶ L :=
  homOfPoints (leviRetractionPoints l r hn)
    (fun _ _ => leviComponent_comp l r _ _)

@[simp] theorem comp_leviRetraction (hn : (SubgroupFunctor.range r).IsNormal)
    {T : Over S} (x : T ⟶ P.X) :
    x ≫ (leviRetraction l r hn).hom.hom = leviComponent l r x :=
  comp_homOfPoints _ _ _ x

/-- The underlying scheme morphism is the projection of the inverse
multiplication isomorphism. -/
theorem leviRetraction_hom_hom (hn : (SubgroupFunctor.range r).IsNormal) :
    (leviRetraction l r hn).hom.hom =
      inv (subgroupMultiplication l r) ≫ fst L.X U.X := by
  simpa only [Category.id_comp, leviComponent] using
    comp_leviRetraction l r hn (𝟙 P.X)

@[simp] theorem levi_comp_leviRetraction (hn : (SubgroupFunctor.range r).IsNormal) :
    l ≫ leviRetraction l r hn = 𝟙 L := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_leviRetraction,
    leviComponent_comp_levi, Grp.id_hom_hom, Category.comp_id]

/-- The all-test kernel of the retraction is exactly the original radical
range, with no passage to rational points or sheafification. -/
theorem comp_leviRetraction_eq_one_iff (hn : (SubgroupFunctor.range r).IsNormal)
    {T : Over S} (x : T ⟶ P.X) :
    x ≫ (leviRetraction l r hn).hom.hom = 1 ↔
      x ∈ (SubgroupFunctor.range r).carrier T := by
  rw [comp_leviRetraction]
  constructor
  · intro hx
    refine ⟨radicalComponent l r x, ?_⟩
    have h := leviComponent_mul_radicalComponent l r x
    rwa [hx, MonObj.one_comp, one_mul] at h
  · rintro ⟨n, rfl⟩
    exact leviComponent_comp_radical l r n

end Base

section Field

variable {k : Type u} [Field k]
  {L P : GroupScheme (Spec (CommRingCat.of k))} {l : L ⟶ P}

/-- A rational Levi supplies a retraction with a represented geometric
unipotent radical as its exact all-test kernel. -/
theorem IsRationalLeviSubgroup.exists_unipotentRadical_retraction
    (hl : IsRationalLeviSubgroup l) :
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (r : U ⟶ P) (q : P ⟶ L),
      LeviSubgroup.IsGeometricUnipotentRadical r ∧
        IsIso (subgroupMultiplication l r) ∧ l ≫ q = 𝟙 L ∧
          ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ P.X),
            x ≫ q.hom.hom = 1 ↔ x ∈ (SubgroupFunctor.range r).carrier T := by
  obtain ⟨U, r, hr, hmul⟩ := hl.exists_unipotentRadical
  let : IsIso (subgroupMultiplication l r) := hmul
  exact ⟨U, r, leviRetraction l r hr.1.isNormal, hr, hmul,
    levi_comp_leviRetraction l r hr.1.isNormal,
    fun _ x => comp_leviRetraction_eq_one_iff l r hr.1.isNormal x⟩

end Field

end Langlands.GroupScheme
