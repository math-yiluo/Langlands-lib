import Langlands.Cohomology.DivisibleSystem.TotalComparison
import Langlands.Cohomology.DivisibleSystem.StandardExact
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-!
# The totalized augmentation is a quasi-isomorphism

Harris 1999, §2, p.306, forms the simple complex `C_m^{•,H}` of the double complex of the
canonical resolutions (2.5) of the `M_m^{q,H}`; after the direct limit over `H` he asserts the
quasi-isomorphism (2.6). This module proves the level-`H` step: the totalized augmentation of the
`Total` module is a quasi-isomorphism whenever `F ε` has a natural section for a faithful exact
functor `F` (a `StandardContraction`). After `F`, the section gives a homotopy equivalence of
total complexes; no vanishing hypothesis is needed for this. Composed with the isomorphism of the
`TotalComparison` module (for `K` vanishing in degrees `q ≥ N`), it gives quasi-isomorphisms to
`K` extended to `ℤ`, in particular from Harris's `C_m^{•,H}` to the `H`-invariant section
complexes.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u v' u' uR uG

section TotalMap

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B]
  (F : A ⥤ B) [PreservesFiniteColimits F] {N : ℕ}
  (Y : HomologicalComplex₂ A (upFin N) (ComplexShape.down ℕ)) (n : ℤ)

/-- After a functor preserving finite colimits, the degree `n` term of the total complex is still
the coproduct of the summands of total degree `n`. -/
def totalMapIsColimit :
    IsColimit (Cofan.mk (F.obj ((Y.total (ComplexShape.up ℤ)).X n))
      (fun i => F.map (Y.ιTotal (ComplexShape.up ℤ) i.1.1 i.1.2 n i.2)) :
        Cofan fun i : upFinFiber N n => F.obj ((Y.X i.1.1).X i.1.2)) :=
  isColimitCofanMkObjOfIsColimit F _ _ (Y.toGradedObject.isColimitCofanMapObj _ n)

variable {F Y n}

/-- A morphism out of `F` of the degree `n` term of the total complex, given on the summands. -/
def totalMapDesc {Z : B}
    (φ : ∀ (q : Fin N) (r : ℕ)
      (_ : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) = n),
      F.obj ((Y.X q).X r) ⟶ Z) :
    F.obj ((Y.total (ComplexShape.up ℤ)).X n) ⟶ Z :=
  Cofan.IsColimit.desc (totalMapIsColimit F Y n) (fun i => φ i.1.1 i.1.2 i.2)

@[reassoc]
lemma map_ιTotal_totalMapDesc {Z : B}
    (φ : ∀ (q : Fin N) (r : ℕ)
      (_ : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) = n),
      F.obj ((Y.X q).X r) ⟶ Z) (q : Fin N) (r : ℕ)
    (h : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) = n) :
    F.map (Y.ιTotal (ComplexShape.up ℤ) q r n h) ≫ totalMapDesc φ = φ q r h :=
  Cofan.IsColimit.fac (totalMapIsColimit F Y n) _ ⟨(q, r), h⟩

lemma totalMap_hom_ext {Z : B} {g₁ g₂ : F.obj ((Y.total (ComplexShape.up ℤ)).X n) ⟶ Z}
    (h : ∀ (q : Fin N) (r : ℕ)
      (hqr : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) = n),
      F.map (Y.ιTotal (ComplexShape.up ℤ) q r n hqr) ≫ g₁ =
        F.map (Y.ιTotal (ComplexShape.up ℤ) q r n hqr) ≫ g₂) :
    g₁ = g₂ :=
  Cofan.IsColimit.hom_ext (totalMapIsColimit F Y n) _ _ (fun i => h i.1.1 i.1.2 i.2)

end TotalMap

section Rows

variable {A : Type u} [Category.{v} A] [Abelian A] (N : ℕ) (P : A ⥤ A) (ε : P ⟶ 𝟭 A)
  [P.Additive] (L : CochainComplex A ℕ)

/-- The rows `q < N` of the double complex of standard resolutions of `L`: the term at `(q, r)`
is `P^(r+1)` applied to the degree `q` term of `L`. -/
abbrev standardRows : HomologicalComplex₂ A (upFin N) (ComplexShape.down ℕ) :=
  ((upFinEmbedding N).restrictionFunctor _).obj
    (((standardResolution P ε).mapHomologicalComplex (ComplexShape.up ℕ)).obj L)

/-- The totalized augmentation at a single level: from the total complex of `standardRows` to
the total complex of the rows `q < N` of `L` placed in resolution degree `0`. -/
abbrev standardRowsAugmentation :
    (standardRows N P ε L).total (ComplexShape.up ℤ) ⟶
      (columnRestriction N L).total (ComplexShape.up ℤ) :=
  HomologicalComplex₂.total.map (((upFinEmbedding N).restrictionFunctor _).map
    ((NatTrans.mapHomologicalComplex (standardResolutionAugmentation P ε)
      (ComplexShape.up ℕ)).app L)) _

/-- The component at `(q, r)` of the augmentation of `standardRows`, typed with the two double
complexes: the augmentation of the standard resolution of `L^q` in degree `r`. -/
def standardRowsAugmentationApp (q : Fin N) (r : ℕ) :
    ((standardRows N P ε L).X q).X r ⟶ ((columnRestriction N L).X q).X r :=
  ((standardResolutionAugmentation P ε).app (L.X q)).f r

@[reassoc]
lemma ιTotal_standardRowsAugmentation (n : ℤ) (q : Fin N) (r : ℕ)
    (h : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) = n) :
    (standardRows N P ε L).ιTotal (ComplexShape.up ℤ) q r n h ≫
        (standardRowsAugmentation N P ε L).f n =
      standardRowsAugmentationApp N P ε L q r ≫
        (columnRestriction N L).ιTotal (ComplexShape.up ℤ) q r n h :=
  HomologicalComplex₂.ιTotal_map _ _ _ _ _ _ _ h

/-- The horizontal differential of `standardRows` on the summand `(q, r)`, towards degree `j` of
the total complex (Mathlib's `HomologicalComplex₂.d₁`, typed with the total complex). -/
def standardRowsD₁ (q : Fin N) (r : ℕ) (j : ℤ) :
    ((standardRows N P ε L).X q).X r ⟶ ((standardRows N P ε L).total (ComplexShape.up ℤ)).X j :=
  (standardRows N P ε L).d₁ (ComplexShape.up ℤ) q r j

/-- The vertical differential of `standardRows` on the summand `(q, r)`, towards degree `j` of
the total complex (Mathlib's `HomologicalComplex₂.d₂`, typed with the total complex). -/
def standardRowsD₂ (q : Fin N) (r : ℕ) (j : ℤ) :
    ((standardRows N P ε L).X q).X r ⟶ ((standardRows N P ε L).total (ComplexShape.up ℤ)).X j :=
  (standardRows N P ε L).d₂ (ComplexShape.up ℤ) q r j

lemma ιTotal_standardRows_d (q : Fin N) (r : ℕ) (i j : ℤ)
    (h : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) = i) :
    (standardRows N P ε L).ιTotal (ComplexShape.up ℤ) q r i h ≫
        ((standardRows N P ε L).total (ComplexShape.up ℤ)).d i j =
      standardRowsD₁ N P ε L q r j + standardRowsD₂ N P ε L q r j := by
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add, HomologicalComplex₂.ι_D₁,
    HomologicalComplex₂.ι_D₂]
  rfl

lemma standardRowsD₁_eq {q q' : Fin N} (hq : (upFin N).Rel q q') (r : ℕ) (j : ℤ)
    (h : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q', r) = j) :
    standardRowsD₁ N P ε L q r j =
      ComplexShape.ε₁ (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) •
        (((standardRows N P ε L).d q q').f r ≫
          (standardRows N P ε L).ιTotal (ComplexShape.up ℤ) q' r j h) :=
  HomologicalComplex₂.d₁_eq _ _ hq r j h

lemma standardRowsD₁_eq_zero (q : Fin N) (r : ℕ) (j : ℤ)
    (hq : ¬ (upFin N).Rel q ((upFin N).next q)) :
    standardRowsD₁ N P ε L q r j = 0 :=
  HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ hq

lemma standardRowsD₂_eq (q : Fin N) {r r' : ℕ} (hr : (ComplexShape.down ℕ).Rel r r') (j : ℤ)
    (h : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r') = j) :
    standardRowsD₂ N P ε L q r j =
      ComplexShape.ε₂ (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) •
        (((standardRows N P ε L).X q).d r r' ≫
          (standardRows N P ε L).ιTotal (ComplexShape.up ℤ) q r' j h) :=
  HomologicalComplex₂.d₂_eq _ _ q hr j h

lemma standardRowsD₂_zero (q : Fin N) (j : ℤ) : standardRowsD₂ N P ε L q 0 j = 0 :=
  HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ fun h0 => Nat.succ_ne_zero _ h0

end Rows

namespace StandardContraction

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B] [Abelian B]
  {F : A ⥤ B} {P : A ⥤ A} {ε : P ⟶ 𝟭 A} (c : StandardContraction F P ε) [P.Additive] (N : ℕ)
  (L : CochainComplex A ℕ)

section Components

/-- `σ` on the summand `(q, r)` of `standardRows`, typed with the double complex: the component
`F (P^(r+1) L^q) ⟶ F (P^(r+2) L^q)`. -/
def rowσ (q : Fin N) (r : ℕ) :
    F.obj (((standardRows N P ε L).X q).X r) ⟶ F.obj (((standardRows N P ε L).X q).X (r + 1)) :=
  c.app (r + 1) (L.X q)

/-- `σ : F L^q ⟶ F (P L^q)`, from the summand `(q, 0)` of the rows of `L` in resolution degree `0`
to the summand `(q, 0)` of `standardRows`. -/
def colσ (q : Fin N) :
    F.obj (((columnRestriction N L).X q).X 0) ⟶ F.obj (((standardRows N P ε L).X q).X 0) :=
  c.app 0 (L.X q)

omit [Abelian B] in
lemma rowσ_naturality (q q' : Fin N) (r : ℕ) :
    F.map (((standardRows N P ε L).d q q').f r) ≫ c.rowσ N L q' r =
      c.rowσ N L q r ≫ F.map (((standardRows N P ε L).d q q').f (r + 1)) :=
  c.σ.naturality ((standardPow P (r + 1)).map (L.d q q'))

omit [Abelian B] in
lemma colσ_naturality (q q' : Fin N) :
    F.map (((columnRestriction N L).d q q').f 0) ≫ c.colσ N L q' =
      c.colσ N L q ≫ F.map (((standardRows N P ε L).d q q').f 0) :=
  (congrArg (fun g => F.map g ≫ c.colσ N L q')
    (ChainComplex.single₀_map_f_zero (L.d q q'))).trans (c.σ.naturality (L.d q q'))

omit [Abelian B] in
lemma colσ_comp (q : Fin N) :
    c.colσ N L q ≫ F.map (standardRowsAugmentationApp N P ε L q 0) = 𝟙 _ :=
  (congrArg (fun g => c.colσ N L q ≫ F.map g)
    (augmentation_app_f_zero (P := P) (ε := ε) (L.X q))).trans (c.σ_comp (L.X q))

end Components

variable [F.Additive]

section Identities

/-- The contraction identity on the column `q` in resolution degree `r + 1`. -/
lemma rowσ_identity (q : Fin N) (r : ℕ) :
    c.rowσ N L q (r + 1) ≫ F.map (((standardRows N P ε L).X q).d (r + 2) (r + 1)) +
      F.map (((standardRows N P ε L).X q).d (r + 1) r) ≫ c.rowσ N L q r = 𝟙 _ := by
  have h₁ : ((standardRows N P ε L).X q).d (r + 2) (r + 1) =
      (standardDifferential P ε (r + 2)).app (L.X q) :=
    standardResolution_obj_d P ε (L.X q) (r + 1)
  have h₂ : ((standardRows N P ε L).X q).d (r + 1) r =
      (standardDifferential P ε (r + 1)).app (L.X q) :=
    standardResolution_obj_d P ε (L.X q) r
  rw [h₁, h₂]
  exact c.identity' (r + 1) (L.X q)

/-- The contraction identity on the column `q` in resolution degree `0`, where the differential
`d_0` is the augmentation. -/
lemma rowσ_identity_zero (q : Fin N) :
    c.rowσ N L q 0 ≫ F.map (((standardRows N P ε L).X q).d 1 0) +
      F.map (standardRowsAugmentationApp N P ε L q 0) ≫ c.colσ N L q = 𝟙 _ := by
  have h₁ : ((standardRows N P ε L).X q).d 1 0 = (standardDifferential P ε 1).app (L.X q) :=
    standardResolution_obj_d P ε (L.X q) 0
  have h₂ : standardRowsAugmentationApp N P ε L q 0 = (standardDifferential P ε 0).app (L.X q) :=
    augmentation_app_f_zero (P := P) (ε := ε) (L.X q)
  rw [h₁, h₂]
  exact c.identity' 0 (L.X q)

end Identities

variable [PreservesFiniteColimits F]

section Section

/-- The section on the summand `(q, r)` of degree `n`: `σ` followed by the inclusion of the
summand `(q, 0)` of the total complex of `standardRows` if `r = 0`, and `0` otherwise (the
summand is then zero). -/
def totalSectionSummand (n : ℤ) (q : Fin N) :
    (r : ℕ) → ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) = n →
      (F.obj (((columnRestriction N L).X q).X r) ⟶
        F.obj (((standardRows N P ε L).total (ComplexShape.up ℤ)).X n))
  | 0, h => c.colσ N L q ≫ F.map ((standardRows N P ε L).ιTotal (ComplexShape.up ℤ) q 0 n h)
  | _ + 1, _ => 0

omit [F.Additive] [PreservesFiniteColimits F] in
lemma totalSectionSummand_zero (n : ℤ) (q : Fin N)
    (h : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, 0) = n) :
    c.totalSectionSummand N L n q 0 h =
      c.colσ N L q ≫ F.map ((standardRows N P ε L).ιTotal (ComplexShape.up ℤ) q 0 n h) :=
  rfl

omit [F.Additive] [PreservesFiniteColimits F] in
lemma totalSectionSummand_succ (n : ℤ) (q : Fin N) (r : ℕ)
    (h : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r + 1) = n) :
    c.totalSectionSummand N L n q (r + 1) h = 0 :=
  rfl

/-- Degree `n` of the section `F (Tot (L in resolution degree 0)) ⟶ F (Tot (standardRows))`. -/
def totalSectionF (n : ℤ) :
    F.obj (((columnRestriction N L).total (ComplexShape.up ℤ)).X n) ⟶
      F.obj (((standardRows N P ε L).total (ComplexShape.up ℤ)).X n) :=
  totalMapDesc (fun q r h => c.totalSectionSummand N L n q r h)

omit [F.Additive] in
@[reassoc]
lemma map_ιTotal_totalSectionF (n : ℤ) (q : Fin N) (r : ℕ)
    (h : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) = n) :
    F.map ((columnRestriction N L).ιTotal (ComplexShape.up ℤ) q r n h) ≫
        c.totalSectionF N L n =
      c.totalSectionSummand N L n q r h :=
  map_ιTotal_totalMapDesc _ q r h

/-- The section commutes with the differentials, by naturality of `σ`. -/
lemma totalSectionF_comm (n n' : ℤ) (hnn' : (ComplexShape.up ℤ).Rel n n') :
    c.totalSectionF N L n ≫ F.map (((standardRows N P ε L).total (ComplexShape.up ℤ)).d n n') =
      F.map (((columnRestriction N L).total (ComplexShape.up ℤ)).d n n') ≫
        c.totalSectionF N L n' := by
  have hnn'' : n + 1 = n' := hnn'
  refine totalMap_hom_ext fun q r h => ?_
  cases r with
  | succ r => exact (F.map_isZero (isZero_columnZero_X_X_succ L q r)).eq_of_src _ _
  | zero =>
    have hq : ((q : ℕ) : ℤ) = n := by
      have h' : ((q : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = n := h
      simpa using h'
    have hd₂ : ¬ (ComplexShape.down ℕ).Rel 0 ((ComplexShape.down ℕ).next 0) :=
      fun h0 => Nat.succ_ne_zero _ h0
    rw [map_ιTotal_totalSectionF_assoc, totalSectionSummand_zero, Category.assoc,
      ← F.map_comp, ← F.map_comp_assoc, HomologicalComplex₂.total_d, HomologicalComplex₂.total_d,
      Preadditive.comp_add, Preadditive.comp_add, HomologicalComplex₂.ι_D₁,
      HomologicalComplex₂.ι_D₂, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
      HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ hd₂, HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ hd₂,
      add_zero, add_zero]
    by_cases hqN : (q : ℕ) + 1 < N
    · have hrel : (upFin N).Rel q ⟨(q : ℕ) + 1, hqN⟩ := rfl
      have hπ : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ)
          (⟨(q : ℕ) + 1, hqN⟩, 0) = n' := by
        rw [upFin_π]
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
        omega
      have hε : ComplexShape.ε₁ (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, 0) = 1 :=
        rfl
      rw [HomologicalComplex₂.d₁_eq _ _ hrel 0 n' hπ, HomologicalComplex₂.d₁_eq _ _ hrel 0 n' hπ,
        hε, one_smul, one_smul, F.map_comp, F.map_comp, Category.assoc,
        map_ιTotal_totalSectionF, totalSectionSummand_zero, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ F.map ((standardRows N P ε L).ιTotal (ComplexShape.up ℤ)
        ⟨(q : ℕ) + 1, hqN⟩ 0 n' hπ)) (c.colσ_naturality N L q ⟨(q : ℕ) + 1, hqN⟩).symm
    · have hnext : ¬ (upFin N).Rel q ((upFin N).next q) := fun hr => by
        have hr' : (q : ℕ) + 1 = ((upFin N).next q : ℕ) := hr
        have := ((upFin N).next q).isLt
        omega
      rw [HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ hnext,
        HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ hnext, F.map_zero, F.map_zero, comp_zero,
        zero_comp]

/-- The section `F (Tot (L in resolution degree 0)) ⟶ F (Tot (standardRows))`, given on the
summand `(q, 0)` by `σ : F (L^q) ⟶ F (P L^q)`. -/
def totalSection :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((columnRestriction N L).total (ComplexShape.up ℤ)) ⟶
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((standardRows N P ε L).total (ComplexShape.up ℤ)) where
  f n := c.totalSectionF N L n
  comm' n n' h := c.totalSectionF_comm N L n n' h

lemma totalSectionF_comp (n : ℤ) :
    c.totalSectionF N L n ≫ F.map ((standardRowsAugmentation N P ε L).f n) = 𝟙 _ := by
  refine totalMap_hom_ext fun q r h => ?_
  rw [map_ιTotal_totalSectionF_assoc, Category.comp_id]
  cases r with
  | succ r => exact (F.map_isZero (isZero_columnZero_X_X_succ L q r)).eq_of_src _ _
  | zero =>
    rw [totalSectionSummand_zero, Category.assoc, ← F.map_comp, ιTotal_standardRowsAugmentation,
      F.map_comp, ← Category.assoc, c.colσ_comp, Category.id_comp]

/-- The section is a section of `F` of the totalized augmentation. -/
lemma totalSection_comp :
    c.totalSection N L ≫
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (standardRowsAugmentation N P ε L) =
      𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun n => c.totalSectionF_comp N L n

end Section

section Homotopy

/-- The contracting homotopy on the summand `(q, r)` of degree `n`, towards degree `m`:
`(-1)^q σ` into the summand `(q, r + 1)` if that summand has degree `m`, and `0` otherwise. -/
def totalHomotopySummand (n m : ℤ) (q : Fin N) (r : ℕ)
    (_ : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) = n) :
    F.obj (((standardRows N P ε L).X q).X r) ⟶
      F.obj (((standardRows N P ε L).total (ComplexShape.up ℤ)).X m) :=
  if hm : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r + 1) = m then
    ((q : ℕ) : ℤ).negOnePow • (c.rowσ N L q r ≫
      F.map ((standardRows N P ε L).ιTotal (ComplexShape.up ℤ) q (r + 1) m hm))
  else 0

omit [F.Additive] [PreservesFiniteColimits F] in
lemma totalHomotopySummand_eq (n m : ℤ) (q : Fin N) (r : ℕ)
    (h : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) = n)
    (hm : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r + 1) = m) :
    c.totalHomotopySummand N L n m q r h = ((q : ℕ) : ℤ).negOnePow • (c.rowσ N L q r ≫
      F.map ((standardRows N P ε L).ιTotal (ComplexShape.up ℤ) q (r + 1) m hm)) :=
  dite_eq_left hm

/-- The contracting homotopy from degree `n` to degree `m` of `F (Tot (standardRows))`. -/
def totalHomotopyF (n m : ℤ) :
    F.obj (((standardRows N P ε L).total (ComplexShape.up ℤ)).X n) ⟶
      F.obj (((standardRows N P ε L).total (ComplexShape.up ℤ)).X m) :=
  totalMapDesc (fun q r h => c.totalHomotopySummand N L n m q r h)

omit [F.Additive] in
@[reassoc]
lemma map_ιTotal_totalHomotopyF (n m : ℤ) (q : Fin N) (r : ℕ)
    (h : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) = n) :
    F.map ((standardRows N P ε L).ιTotal (ComplexShape.up ℤ) q r n h) ≫
        c.totalHomotopyF N L n m =
      c.totalHomotopySummand N L n m q r h :=
  map_ιTotal_totalMapDesc _ q r h

omit [F.Additive] in
lemma totalHomotopyF_eq_zero (n m : ℤ) (hnm : ¬ (ComplexShape.up ℤ).Rel m n) :
    c.totalHomotopyF N L n m = 0 := by
  refine totalMap_hom_ext fun q r h => ?_
  rw [map_ιTotal_totalHomotopyF, comp_zero]
  refine dite_eq_right fun hm => hnm ?_
  rw [upFin_π] at h hm
  change m + 1 = n
  push_cast at hm
  omega

/-- The row parts of `d h` and `h d` cancel, by naturality of `σ` and the sign `(-1)^q`. -/
lemma row_cancel (q : Fin N) (r : ℕ) (i : ℤ)
    (h : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) = i) :
    F.map (standardRowsD₁ N P ε L q r (i + 1)) ≫ c.totalHomotopyF N L (i + 1) i +
      ((q : ℕ) : ℤ).negOnePow • (c.rowσ N L q r ≫
        F.map (standardRowsD₁ N P ε L q (r + 1) i)) = 0 := by
  by_cases hqN : (q : ℕ) + 1 < N
  · have hrel : (upFin N).Rel q ⟨(q : ℕ) + 1, hqN⟩ := rfl
    rw [upFin_π] at h
    have h₁ : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ)
        (⟨(q : ℕ) + 1, hqN⟩, r) = i + 1 := by
      rw [upFin_π]
      push_cast
      omega
    have h₂ : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ)
        (⟨(q : ℕ) + 1, hqN⟩, r + 1) = i := by
      rw [upFin_π]
      push_cast
      omega
    have hε : ∀ x, ComplexShape.ε₁ (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) x = 1 :=
      fun _ => rfl
    have hsign : (((⟨(q : ℕ) + 1, hqN⟩ : Fin N) : ℕ) : ℤ).negOnePow =
        -((q : ℕ) : ℤ).negOnePow := by
      change (((q : ℕ) + 1 : ℕ) : ℤ).negOnePow = _
      rw [Nat.cast_succ, Int.negOnePow_succ]
    rw [standardRowsD₁_eq _ _ _ _ hrel r (i + 1) h₁, standardRowsD₁_eq _ _ _ _ hrel (r + 1) i h₂,
      hε, hε, one_smul, one_smul, F.map_comp, F.map_comp, Category.assoc,
      map_ιTotal_totalHomotopyF, totalHomotopySummand_eq _ _ _ _ _ _ _ _ h₂,
      Linear.comp_units_smul, hsign, Units.neg_smul, ← Category.assoc, c.rowσ_naturality,
      Category.assoc, neg_add_cancel]
  · have hnext : ¬ (upFin N).Rel q ((upFin N).next q) := fun hr => by
      have hr' : (q : ℕ) + 1 = ((upFin N).next q : ℕ) := hr
      have := ((upFin N).next q).isLt
      omega
    rw [standardRowsD₁_eq_zero _ _ _ _ _ _ _ hnext, standardRowsD₁_eq_zero _ _ _ _ _ _ _ hnext,
      F.map_zero, F.map_zero, zero_comp, comp_zero, smul_zero, add_zero]

/-- The column parts of `d h` and `h d`, together with `F a ≫ s`, give the identity: this is the
contraction identity of `σ` on the column `q`. -/
lemma col_identity (q : Fin N) (r : ℕ) (i : ℤ)
    (h : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) = i) :
    F.map (standardRowsD₂ N P ε L q r (i + 1)) ≫ c.totalHomotopyF N L (i + 1) i +
      ((q : ℕ) : ℤ).negOnePow • (c.rowσ N L q r ≫
        F.map (standardRowsD₂ N P ε L q (r + 1) i)) +
      F.map ((standardRows N P ε L).ιTotal (ComplexShape.up ℤ) q r i h ≫
        (standardRowsAugmentation N P ε L).f i) ≫ c.totalSectionF N L i =
    F.map ((standardRows N P ε L).ιTotal (ComplexShape.up ℤ) q r i h) := by
  have hrel : (ComplexShape.down ℕ).Rel (r + 1) r := rfl
  have hε : ComplexShape.ε₂ (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r + 1) =
      ((q : ℕ) : ℤ).negOnePow := rfl
  have hcol : ((q : ℕ) : ℤ).negOnePow • (c.rowσ N L q r ≫
      F.map (standardRowsD₂ N P ε L q (r + 1) i)) =
      c.rowσ N L q r ≫ F.map (((standardRows N P ε L).X q).d (r + 1) r) ≫
        F.map ((standardRows N P ε L).ιTotal (ComplexShape.up ℤ) q r i h) := by
    rw [standardRowsD₂_eq _ _ _ _ q hrel i h, hε, Functor.map_units_smul,
      Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul, F.map_comp]
  rw [hcol, ιTotal_standardRowsAugmentation, F.map_comp, Category.assoc,
    map_ιTotal_totalSectionF]
  cases r with
  | zero =>
    rw [standardRowsD₂_zero, F.map_zero, zero_comp, zero_add, totalSectionSummand_zero,
      ← Category.assoc, ← Category.assoc, ← Preadditive.add_comp]
    exact (congrArg (· ≫ _) (c.rowσ_identity_zero N L q)).trans (Category.id_comp _)
  | succ r =>
    rw [upFin_π] at h
    have h₁ : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) =
        i + 1 := by
      rw [upFin_π]
      push_cast at h ⊢
      omega
    have hm : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r + 1) =
        i := by
      rw [upFin_π]
      push_cast at h ⊢
      omega
    have hε' : ComplexShape.ε₂ (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r + 1) =
        ((q : ℕ) : ℤ).negOnePow := rfl
    have hrel' : (ComplexShape.down ℕ).Rel (r + 1) r := rfl
    rw [standardRowsD₂_eq _ _ _ _ q hrel' (i + 1) h₁, hε', Functor.map_units_smul,
      Linear.units_smul_comp, F.map_comp, Category.assoc, map_ιTotal_totalHomotopyF,
      totalHomotopySummand_eq _ _ _ _ _ _ _ _ hm, Linear.comp_units_smul, smul_smul,
      Int.units_mul_self, one_smul, totalSectionSummand_succ, comp_zero, add_zero,
      ← Category.assoc, ← Category.assoc, ← Preadditive.add_comp]
    exact (congrArg (· ≫ _) ((add_comm _ _).trans (c.rowσ_identity N L q r))).trans
      (Category.id_comp _)

/-- The homotopy identity on the summand `(q, r)` of degree `i`. -/
lemma homotopy_summand (q : Fin N) (r : ℕ) (i : ℤ)
    (h : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) = i) :
    F.map ((standardRows N P ε L).ιTotal (ComplexShape.up ℤ) q r i h) =
      F.map ((standardRows N P ε L).ιTotal (ComplexShape.up ℤ) q r i h) ≫
        (F.map (((standardRows N P ε L).total (ComplexShape.up ℤ)).d i (i + 1)) ≫
            c.totalHomotopyF N L (i + 1) i +
          c.totalHomotopyF N L i (i - 1) ≫
            F.map (((standardRows N P ε L).total (ComplexShape.up ℤ)).d (i - 1) i) +
          F.map ((standardRowsAugmentation N P ε L).f i) ≫ c.totalSectionF N L i) := by
  have h' : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r + 1) =
      i - 1 := by
    rw [upFin_π] at h ⊢
    push_cast
    omega
  have T₁ : F.map ((standardRows N P ε L).ιTotal (ComplexShape.up ℤ) q r i h) ≫
      F.map (((standardRows N P ε L).total (ComplexShape.up ℤ)).d i (i + 1)) ≫
        c.totalHomotopyF N L (i + 1) i =
      F.map (standardRowsD₁ N P ε L q r (i + 1)) ≫ c.totalHomotopyF N L (i + 1) i +
        F.map (standardRowsD₂ N P ε L q r (i + 1)) ≫ c.totalHomotopyF N L (i + 1) i := by
    rw [← Category.assoc, ← F.map_comp, ιTotal_standardRows_d, F.map_add, Preadditive.add_comp]
  have T₂ : F.map ((standardRows N P ε L).ιTotal (ComplexShape.up ℤ) q r i h) ≫
      c.totalHomotopyF N L i (i - 1) ≫
        F.map (((standardRows N P ε L).total (ComplexShape.up ℤ)).d (i - 1) i) =
      ((q : ℕ) : ℤ).negOnePow • (c.rowσ N L q r ≫
          F.map (standardRowsD₁ N P ε L q (r + 1) i)) +
        ((q : ℕ) : ℤ).negOnePow • (c.rowσ N L q r ≫
          F.map (standardRowsD₂ N P ε L q (r + 1) i)) := by
    rw [map_ιTotal_totalHomotopyF_assoc, totalHomotopySummand_eq _ _ _ _ _ _ _ _ h',
      Linear.units_smul_comp, Category.assoc, ← F.map_comp, ιTotal_standardRows_d, F.map_add,
      Preadditive.comp_add, smul_add]
  have T₃ : F.map ((standardRows N P ε L).ιTotal (ComplexShape.up ℤ) q r i h) ≫
      F.map ((standardRowsAugmentation N P ε L).f i) ≫ c.totalSectionF N L i =
      F.map ((standardRows N P ε L).ιTotal (ComplexShape.up ℤ) q r i h ≫
        (standardRowsAugmentation N P ε L).f i) ≫ c.totalSectionF N L i :=
    (F.map_comp_assoc _ _ _).symm
  rw [Preadditive.comp_add, Preadditive.comp_add, T₁, T₂, T₃]
  refine (c.col_identity N L q r i h).symm.trans ?_
  rw [eq_neg_of_add_eq_zero_left (c.row_cancel N L q r i h)]
  abel

/-- The contracting homotopy between the identity of `F (Tot (standardRows))` and `F` of the
totalized augmentation followed by the section. -/
def totalHomotopy :
    Homotopy (𝟙 ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((standardRows N P ε L).total (ComplexShape.up ℤ))))
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (standardRowsAugmentation N P ε L) ≫
        c.totalSection N L) where
  hom i j := c.totalHomotopyF N L i j
  zero i j hij := c.totalHomotopyF_eq_zero N L i j hij
  comm i := by
    refine totalMap_hom_ext fun q r h => ?_
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)]
    exact (Category.comp_id _).trans (c.homotopy_summand N L q r i h)

end Homotopy

section Equiv

/-- `F` of the totalized augmentation of `standardRows` is a homotopy equivalence, with homotopy
inverse the section `totalSection`. -/
def totalHomotopyEquiv :
    HomotopyEquiv ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((standardRows N P ε L).total (ComplexShape.up ℤ)))
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((columnRestriction N L).total (ComplexShape.up ℤ))) where
  hom := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (standardRowsAugmentation N P ε L)
  inv := c.totalSection N L
  homotopyHomInvId := (c.totalHomotopy N L).symm
  homotopyInvHomId := Homotopy.ofEq (c.totalSection_comp N L)

include c in
/-- The totalized augmentation of `standardRows` is a quasi-isomorphism, for `F` faithful and
exact. -/
theorem quasiIso_standardRowsAugmentation [F.Faithful] [PreservesFiniteLimits F] :
    QuasiIso (standardRowsAugmentation N P ε L) := by
  have : F.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels F
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ F]
  exact (c.totalHomotopyEquiv N L).quasiIso_hom

end Equiv

end StandardContraction

namespace DivisibleSystem

section Standard

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B] [Abelian B]
  {F : A ⥤ B} {P : A ⥤ A} {ε : P ⟶ 𝟭 A} [F.Additive] [F.Faithful] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  {ℓ : ℕ} (N : ℕ)

/-- Each level of the totalized augmentation of an `ℓ`-divisible system of cochain complexes is a
quasi-isomorphism. -/
theorem quasiIso_standardTotalSystemAugmentation (c : StandardContraction F P ε)
    (K : DivisibleSystem (CochainComplex A ℕ) ℓ) (m : ℕ) :
    QuasiIso ((K.standardTotalSystemAugmentation N P ε).tower.app (op m)) :=
  c.quasiIso_standardRowsAugmentation N (K.obj m)

/-- For `K` vanishing in degrees `q ≥ N`, each level of the morphism from the total complexes of
the standard resolutions to `K` extended to `ℤ` is a quasi-isomorphism. -/
theorem quasiIso_standardTotalSystemToExtend (c : StandardContraction F P ε)
    (K : DivisibleSystem (CochainComplex A ℕ) ℓ) (hK : ∀ m q, N ≤ q → IsZero ((K.obj m).X q))
    (m : ℕ) :
    QuasiIso ((K.standardTotalSystemToExtend N P ε hK).tower.app (op m)) := by
  have := quasiIso_standardTotalSystemAugmentation N c K m
  have : IsIso ((K.columnTotalSystemComparison N hK).tower.app (op m)) :=
    isIso_columnComparison N (K.obj m) (hK m)
  change QuasiIso ((K.standardTotalSystemAugmentation N P ε).tower.app (op m) ≫
    (K.columnTotalSystemComparison N hK).tower.app (op m))
  infer_instance

end Standard

section Group

variable {k : Type u} [CommRing k] {Γ : Type v} [Group Γ] [Finite Γ] {ℓ : ℕ} (N : ℕ)

/-- Each level of the totalized augmentation along `Ind_1^Γ Res_1^Γ`, `Γ` finite, is a
quasi-isomorphism. -/
theorem quasiIso_groupStandardTotalSystemAugmentation
    (K : DivisibleSystem (CochainComplex (Rep.{max w u v} k Γ) ℕ) ℓ) (m : ℕ) :
    QuasiIso ((K.groupStandardTotalSystemAugmentation N).tower.app (op m)) :=
  quasiIso_standardTotalSystemAugmentation N (indResBotContraction.{w} k Γ) K m

/-- `quasiIso_standardTotalSystemToExtend` for `P = Ind_1^Γ Res_1^Γ`, `Γ` finite. -/
theorem quasiIso_groupStandardTotalSystemToExtend
    (K : DivisibleSystem (CochainComplex (Rep.{max w u v} k Γ) ℕ) ℓ)
    (hK : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) (m : ℕ) :
    QuasiIso ((K.groupStandardTotalSystemToExtend N hK).tower.app (op m)) :=
  quasiIso_standardTotalSystemToExtend N (indResBotContraction.{w} k Γ) K hK m

end Group

section Smooth

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {ℓ : ℕ}
  (N : ℕ) (K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, max w uR uG} R G) ℕ) ℓ)
  (H : Subgroup G) [H.Normal] [H.FiniteIndex]

/-- Each level of `quotientInvariantsTotalSystemToExtend` is a quasi-isomorphism. -/
theorem quasiIso_quotientInvariantsTotalSystemToExtend
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))
    (hN : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) (m : ℕ) :
    QuasiIso ((K.quotientInvariantsTotalSystemToExtend N H hK hN).tower.app (op m)) :=
  quasiIso_groupStandardTotalSystemToExtend N (K.quotientInvariantsComplexes H hK) _ m

end Smooth

section SmoothGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ) (H : Subgroup G) [H.Normal] [H.FiniteIndex]

/-- Each level of the morphism from Harris's `C_m^{•,H}` to the `H`-invariant section complexes
extended to `ℤ` is a quasi-isomorphism. -/
theorem quasiIso_smoothGodementInvariantTotalSystemToExtend
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
        ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
        ((smoothGodementResidualSystem h T (D + 1)).projection hm))) (m : ℕ) :
    QuasiIso ((smoothGodementInvariantTotalSystemToExtend h T D H hterm hres).tower.app
      (op m)) :=
  quasiIso_groupStandardTotalSystemToExtend.{0} (D + 2)
    (smoothGodementTruncatedQuotientInvariantSectionsSystem h T D H hterm hres) _ m

end SmoothGodement

end DivisibleSystem

end Langlands.Cohomology
