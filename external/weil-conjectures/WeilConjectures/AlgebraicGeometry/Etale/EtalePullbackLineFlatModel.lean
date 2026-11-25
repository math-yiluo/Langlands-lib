/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.ConstructibleSheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# Flat constructible pullback and line models

Source: Stacks Project, Tag 0963, lemma-pullback-ctf, with the explicit termwise
line, signed shift, representative comparison and pulled-back trivializing witnesses
(blueprint: lem-sp-etale-pullback-line-flat-model).

The comparison is defined first in the derived-to-model direction using the lax
monoidal localization map. Its invertibility specifies its inverse uniquely, giving
the model-to-derived arrow of the statement without choosing an arbitrary isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u uA vA wA

open CategoryTheory CategoryTheory.Limits MonoidalCategory

/-- Localization's actual tensor comparison with a shifted single sheaf.
Source: Stacks Project Tags 06YU and 0FPQ
(blueprint: lem-sp-etale-pullback-line-flat-model). -/
noncomputable def etaleLineRepresentativeComparison
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
    [HasDerivedCategory.{wA} A] [Abelian.HasFunctorialFlatResolution A]
    (P : CochainComplex A ℤ) (K : _root_.DerivedCategory A)
    (e : K ⟶ _root_.DerivedCategory.Q.obj P) (E : A) (r : ℤ) :
    K ⊗ ((_root_.DerivedCategory.singleFunctor A 0).obj E)⟦r⟧ ⟶
      _root_.DerivedCategory.Q.obj
        ((((tensorRight E).mapHomologicalComplex (.up ℤ)).obj P)⟦r⟧) := by
  let S := (HomologicalComplex.single A (.up ℤ) 0).obj E
  let t : _root_.DerivedCategory.Q.obj P ⊗
      (_root_.DerivedCategory.singleFunctor A 0).obj E ⟶
      _root_.DerivedCategory.Q.obj
        (((tensorRight E).mapHomologicalComplex (.up ℤ)).obj P) :=
    (_root_.DerivedCategory.Q.obj P ◁
      ((_root_.DerivedCategory.singleFunctorIsoCompQ A 0).app E).hom) ≫
      Functor.LaxMonoidal.μ _root_.DerivedCategory.Q P S ≫
      _root_.DerivedCategory.Q.map
        ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor A) E).app P).hom
  exact ((tensorLeft K).commShiftIso r).hom.app
      ((_root_.DerivedCategory.singleFunctor A 0).obj E) ≫
    (shiftFunctor _ r).map ((e ▷ _) ≫ t) ≫
      (_root_.DerivedCategory.Q.commShiftIso r).inv.app _

private theorem line_comparison_isIso
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
    [HasDerivedCategory.{wA} A] [Abelian.HasFunctorialFlatResolution A]
    (P : CochainComplex A ℤ) (K : _root_.DerivedCategory A)
    (e : K ⟶ _root_.DerivedCategory.Q.obj P) [IsIso e] (E : A) (r : ℤ)
    (hP : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P) :
    IsIso (etaleLineRepresentativeComparison P K e E r) := by
  let H := HomotopyCategory.quotient A (.up ℤ)
  let S := (HomologicalComplex.single A (.up ℤ) 0).obj E
  have hP' := (HomotopyCategory.kFlat_quotient_obj_iff P).2 hP
  have := _root_.DerivedCategory.isIso_tensorLeftCounit (H.obj P) hP'
  have hmu : IsIso (Functor.LaxMonoidal.μ _root_.DerivedCategory.Q P S) := by
    change IsIso (((_root_.DerivedCategory.quotientCompQhIso A).inv.app P ⊗ₘ
      (_root_.DerivedCategory.quotientCompQhIso A).inv.app S) ≫
      (Functor.LaxMonoidal.μ _root_.DerivedCategory.Qh (H.obj P) (H.obj S) ≫
        _root_.DerivedCategory.Qh.map (Functor.LaxMonoidal.μ H P S)) ≫
      (_root_.DerivedCategory.quotientCompQhIso A).hom.app (P ⊗ S))
    have : IsIso (Functor.LaxMonoidal.μ _root_.DerivedCategory.Qh (H.obj P) (H.obj S)) :=
      inferInstanceAs (IsIso ((_root_.DerivedCategory.tensorLeftCounit (H.obj P)).app
        (H.obj S)))
    infer_instance
  dsimp only [etaleLineRepresentativeComparison]
  infer_instance

/-- Specialize the canonical comparison to the existing small-etale tensor structures.
Source: Stacks Project Tag 0963 and Tag 06YU
(blueprint: lem-sp-etale-pullback-line-flat-model). -/
noncomputable def etaleLineRepresentativeComparisonOnSite
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : AlgebraicGeometry.Scheme.{u})
    (P : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (h : K ⟶ _root_.DerivedCategory.Q.obj P)
    (E : Sheaf X.smallEtaleTopology A) (r : ℤ) :=
  etaleLineRepresentativeComparison P K h E r

/-- Invertibility of the canonical representative comparison on the small etale site.
Source: Stacks Project Tags 0963 and 06YU
(blueprint: lem-sp-etale-pullback-line-flat-model). -/
def etaleLineRepresentativeComparisonIsIsoOnSite
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : AlgebraicGeometry.Scheme.{u})
    (P : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (h : K ⟶ _root_.DerivedCategory.Q.obj P)
    (E : Sheaf X.smallEtaleTopology A) (r : ℤ) : Prop :=
  IsIso (etaleLineRepresentativeComparisonOnSite A X P K h E r)

namespace AlgebraicGeometry.Etale

variable (R : Type (u + 1)) [CommRing R]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The termwise inverse image, tensor with the specified line and cochain shift.
Source: Stacks Project Tag 0963, finite-complex argument
(blueprint: lem-sp-etale-pullback-line-flat-model). -/
noncomputable def etalePullbackLineModel
    (C : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (r : ℤ) :
    CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ :=
  (((@tensorRight _ _ (Sheaf.monoidalCategory X.smallEtaleTopology
    (ModuleCat.{u + 1} R)) E).mapHomologicalComplex (.up ℤ)).obj
      (((upperStar (ModuleCat.{u + 1} R) f).mapHomologicalComplex (.up ℤ)).obj C))⟦r⟧

/-- The target is the exact derived inverse image of K tensored with the shifted line.
Source: Stacks Project Tag 0963, constant-coefficient derived pullback
(blueprint: lem-sp-etale-pullback-line-flat-model). -/
noncomputable def etalePullbackLineTarget (K : DerivedCategoryModule R Y)
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (r : ℤ) :
    DerivedCategoryModule R X :=
  ((derivedTensor (ModuleCat.{u + 1} R) X).obj
    ((upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategory.obj K)).obj
      (((_root_.DerivedCategory.singleFunctor _ 0).obj E)⟦r⟧)

/-- Exact inverse image's localization comparison, using the prescribed representative.
Source: Stacks Project Tag 0963, exact constant-coefficient inverse image
(blueprint: lem-sp-etale-pullback-line-flat-model). -/
noncomputable def etalePullbackRepresentative
    (C : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
    (K : DerivedCategoryModule R Y) (e : _root_.DerivedCategory.Q.obj C ≅ K) :
    (upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategory.obj K ⟶
    _root_.DerivedCategory.Q.obj
      (((upperStar (ModuleCat.{u + 1} R) f).mapHomologicalComplex (.up ℤ)).obj C) :=
  (upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategory.map e.inv ≫
    (upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategoryFactors.hom.app C

/-- The canonical representative comparison, in the derived-to-model direction.
It uses the specified isomorphism Q(C) = K, exact pullback's localization comparison,
the lax monoidal map of Q, the total-tensor/single-complex identification and the
cochain shift. Its inverse, when invertible, is the required representative-defined map.
Source: Stacks Project Tags 0963, 06YU and 0FPQ
(blueprint: lem-sp-etale-pullback-line-flat-model). -/
noncomputable def etalePullbackLineComparison
    (C : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
    (K : DerivedCategoryModule R Y) (e : _root_.DerivedCategory.Q.obj C ≅ K)
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (r : ℤ) :=
  etaleLineRepresentativeComparisonOnSite (ModuleCat.{u + 1} R) X
    (((upperStar (ModuleCat.{u + 1} R) f).mapHomologicalComplex (.up ℤ)).obj C)
    ((upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategory.obj K)
    (etalePullbackRepresentative R f C K e) E r

/-- The common refinement of the prescribed pulled-back cover and the line's cover.
Source: Stacks Project Tags 095G and 095I, fibre products of trivializing covers
(blueprint: lem-sp-etale-pullback-line-flat-model). -/
noncomputable def etalePullbackLineCover (S : Scheme.Stratification Y) (k : Fin S.n)
    (U : Scheme.Cover.{u} Scheme.etalePrecoverage (S.domain k))
    (V : Scheme.Cover.{u} Scheme.etalePrecoverage X) :
    Scheme.Cover.{u} Scheme.etalePrecoverage ((S.pullback f).domain k) :=
  (U.pullback₂ (pullback.fst (S.immersion k) f)).inter
    (V.pullback₂ ((S.pullback f).immersion k))

/-- All conclusions, including arbitrary prescribed cohomology stratifications and
finite module values on the actual common refinement. The only local instance here is
lexically inside this definition and is the canonical sheaf tensor structure.
Source: Stacks Project Tags 0963, 095G, 095I, 03RZ, 06YQ and 06YU
(blueprint: lem-sp-etale-pullback-line-flat-model). -/
noncomputable def etalePullbackLineAssertions [Finite R]
    (C : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
    (K : DerivedCategoryModule R Y) (e : _root_.DerivedCategory.Q.obj C ≅ K)
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (r a b : ℤ)
    (V : Scheme.Cover.{u} Scheme.etalePrecoverage X) : Prop :=
  let := Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} R)
  let Q := etalePullbackLineModel R f C E r
  (∀ n : ℤ, exactFunctor _ _ (tensorRight (Q.X n))) ∧
  (∀ n : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (Q.X n)) ∧
  (∀ n : ℤ, (n < a - r ∨ b - r < n) → IsZero (Q.X n)) ∧
  (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q ∧
  etaleLineRepresentativeComparisonIsIsoOnSite (ModuleCat.{u + 1} R) X
    (((upperStar (ModuleCat.{u + 1} R) f).mapHomologicalComplex (.up ℤ)).obj C)
    ((upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategory.obj K)
    (etalePullbackRepresentative R f C K e) E r ∧
  (∀ j : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (Q.homology j)) ∧
  DerivedCategory.hasTorAmplitudeIn R X (a - r) (b - r)
    (_root_.DerivedCategory.Q.obj Q) ∧
  ∀ (j : ℤ) (S : Scheme.Stratification Y)
    (d : ∀ k : Fin S.n, Scheme.LocallyConstantDatum
      ((upperStar (ModuleCat.{u + 1} R) (S.immersion k)).obj (C.homology (j + r))))
    (M : ∀ k : Fin S.n, (d k).cover.I₀ → ModuleCat.{u + 1} R),
    (∀ (k : Fin S.n) (i : (d k).cover.I₀), Finite (M k i)) →
    (∀ (k : Fin S.n) (i : (d k).cover.I₀), Nonempty
      ((((upperStar (ModuleCat.{u + 1} R) (S.immersion k)).obj
        (C.homology (j + r))).over ((d k).cover.etalePrecoverageToEtale i)) ≅
        (constantSheaf ((S.domain k).smallEtaleTopology.over
          ((d k).cover.etalePrecoverageToEtale i)) (ModuleCat.{u + 1} R)).obj (M k i))) →
    ∀ k : Fin S.n,
      Nonempty (((upperStar (ModuleCat.{u + 1} R) ((S.pullback f).immersion k)).obj
        (Q.homology j)) ≅
        @tensorObj _ _ (Sheaf.monoidalCategory
          ((S.pullback f).domain k).smallEtaleTopology
            (ModuleCat.{u + 1} R)).toMonoidalCategoryStruct
          ((upperStar (ModuleCat.{u + 1} R) (pullback.fst (S.immersion k) f)).obj
            ((upperStar (ModuleCat.{u + 1} R) (S.immersion k)).obj
              (C.homology (j + r))))
          ((upperStar (ModuleCat.{u + 1} R) ((S.pullback f).immersion k)).obj E)) ∧
      ∀ i : (etalePullbackLineCover f S k (d k).cover V).I₀,
        Nonempty (((upperStar (ModuleCat.{u + 1} R)
          ((etalePullbackLineCover f S k (d k).cover V).f i)).obj
            ((upperStar (ModuleCat.{u + 1} R) ((S.pullback f).immersion k)).obj
              (Q.homology j))) ≅
          (constantSheaf
            ((etalePullbackLineCover f S k (d k).cover V).X i).smallEtaleTopology
              (ModuleCat.{u + 1} R)).obj (M k i.1))

/-- Pullback, termwise line tensor and arbitrary integer shift preserve flat constructible
models, with support and Tor interval [a-r,b-r], the canonical derived comparison and
all prescribed pulled-back cohomology-stratum trivializations.

Source: Stacks Project Tag 0963, lemma-pullback-ctf, explicit finite-complex strengthening
(blueprint: lem-sp-etale-pullback-line-flat-model).

Proof:
1. Lift each geometric point through the prescribed cover V. The stalk of E there
   is R by the given trivialization and the constant-sheaf stalk comparison. Hence E
   is flat. Local constancy and finiteness descend through V, so E is constructible.
2. The source flat-pullback instance preserves flatness of every term of C. Pullback
   stability of constructibility, followed by tensor stability, gives constructibility
   of each term of Q. Its term in degree n is f⁻¹(C^(n+r)) tensor E; exact functors
   preserve zero objects, giving support [a-r,b-r] directly.
3. The source bounded-above flat criterion gives K-flatness of Q and of P = f⁻¹C.
   For the actual comparison, expand the lax tensor map of Q as the tensor map of
   the homotopy quotient followed by that of Qh, transported through quotientCompQhIso.
   The latter is precisely the K-flat tensor counit and is invertible. All other maps
   defining the comparison are isomorphisms, including the prescribed representative,
   exact pullback's localization comparison, the single-complex comparison and shifts.
4. Kernels and cokernels of constructible module sheaves are constructible, giving
   constructibility of the cohomology of Q. Apply torAmplitudeIn_Q_obj_of_flat to Q
   and evaluate its t-structure bounds on each sheaf and degree.
5. Exact pullback and exact tensor with E commute with cohomology. The cochain shift
   comparison identifies H^j(Q) with f⁻¹H^(j+r)(C) tensor E for every integer r.
   Pull back along each prescribed stratum and use the monoidal pullback comparison
   and the cartesian-square composition comparisons to obtain the stated formula.
6. Transport each given over-site trivialization through the equivalence with the
   corresponding scheme's etale site. Pull it and the given trivialization of E to the
   actual fibre-product common refinement. The two projections commute with the maps
   to the stratum and X. Constant-sheaf pullback and its monoidal structure then give
   the constant value M tensor R, and the right unitor identifies this with M. No
   nonemptiness of a stratum or cover member and no sign or positivity assumption on
   r is used.
-/
theorem etale_pullback_line_flat_model [Finite R]
    [IsNoetherian X] [IsNoetherian Y]
    (C : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
    (a b : ℤ) (_hab : a ≤ b)
    (_hflat : ∀ n : ℤ, exactFunctor _ _
      (@tensorRight _ _ (Sheaf.monoidalCategory Y.smallEtaleTopology
        (ModuleCat.{u + 1} R)) (C.X n)))
    (_hc : ∀ n : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (C.X n))
    (_hz : ∀ n : ℤ, (n < a ∨ b < n) → IsZero (C.X n))
    (K : DerivedCategoryModule R Y) (e : _root_.DerivedCategory.Q.obj C ≅ K)
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (r : ℤ)
    (V : Scheme.Cover.{u} Scheme.etalePrecoverage X)
    (_hE : ∀ i : V.I₀, Nonempty
      ((upperStar (ModuleCat.{u + 1} R) (V.f i)).obj E ≅
        (constantSheaf (V.X i).smallEtaleTopology (ModuleCat.{u + 1} R)).obj
          (ModuleCat.of R R))) :
    etalePullbackLineAssertions R f C K e E r a b V := by
  classical
  let := Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} R)
  let Q := etalePullbackLineModel R f C E r
  have hEf : ObjectProperty.flat E := by
    apply (flat_iff_forall_flat_sheafFiber_obj E).2
    intro Ω _ _ s
    obtain ⟨i, t, ht⟩ := V.exists_comp_eq_of_isSepClosed s
    subst s
    let Φ := (Scheme.pointSmallEtale t).ulift.{u + 1}
    let eE := (upperStarCompUliftSheafFiberIso (ModuleCat.{u + 1} R) (V.f i) t).app E
    let eR := Φ.sheafFiber.mapIso (_hE i).some ≪≫
      Φ.sheafFiberConstantSheafIso (ModuleCat.of R R)
    exact (ObjectProperty.flat (A := ModuleCat.{u + 1} R)).prop_of_iso (eE.symm ≪≫ eR).symm
      (ObjectProperty.prop_unit (ObjectProperty.flat (A := ModuleCat.{u + 1} R)))
  have hEc : Scheme.IsConstructibleSheaf E := by
    have hEl (i : V.I₀) : Scheme.IsLocallyConstantSheaf
        ((upperStar (ModuleCat.{u + 1} R) (V.f i)).obj E) := by
      have : (((upperStar (ModuleCat.{u + 1} R) (V.f i)).obj E)).IsConstant
          (V.X i).smallEtaleTopology :=
        Sheaf.isConstant_of_iso _ (_hE i).some
      exact Sheaf.IsConstant.isLocallyConstantSheaf inferInstance
    have hElocal : Scheme.IsLocallyConstantSheaf E :=
      Scheme.IsLocallyConstantSheaf.of_cover V E
    have hEfin (i : V.I₀) : Scheme.IsFiniteSheaf
        ((upperStar (ModuleCat.{u + 1} R) (V.f i)).obj E) := by
      have := Scheme.isFiniteSheaf_constantSheaf
        (X := V.X i) (ModuleCat.of R R)
      exact Scheme.IsFiniteSheaf.of_iso (_hE i).some.symm
    have hEfinit : Scheme.IsFiniteSheaf E := Scheme.IsFiniteSheaf.of_cover V E
    exact Scheme.IsFiniteLocallyConstantSheaf.isConstructibleSheaf
      (F := E) {}
  have hCf (n : ℤ) : ObjectProperty.flat (C.X n) :=
    ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight (C.X n)).symm (_hflat n), _hflat n⟩
  have hQf (n : ℤ) : ObjectProperty.flat (Q.X n) := by
    change ObjectProperty.flat
      ((upperStar (ModuleCat.{u + 1} R) f).obj (C.X (n + r)) ⊗ E)
    exact ObjectProperty.prop_tensor (Functor.PreservesFlat.flat_obj (hCf _)) hEf
  have hQc (n : ℤ) : Scheme.IsConstructibleEtaleModuleSheaf (Q.X n) := by
    apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
    change Scheme.IsConstructibleSheaf
      ((upperStar (ModuleCat.{u + 1} R) f).obj (C.X (n + r)) ⊗ E)
    have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (_hc (n + r))
    exact (Scheme.IsConstructibleSheaf.upperStar f _).tensorObj hEc
  have hQz (n : ℤ) (hn : n < a - r ∨ b - r < n) : IsZero (Q.X n) := by
    change IsZero ((upperStar (ModuleCat.{u + 1} R) f).obj (C.X (n + r)) ⊗ E)
    exact (tensorRight E).map_isZero ((upperStar (ModuleCat.{u + 1} R) f).map_isZero
      (_hz (n + r) (by omega)))
  have : Q.IsStrictlyGE (a - r) := (Q.isStrictlyGE_iff _).2 fun n hn ↦ hQz n (.inl hn)
  have : Q.IsStrictlyLE (b - r) := (Q.isStrictlyLE_iff _).2 fun n hn ↦ hQz n (.inr hn)
  change (∀ n, exactFunctor _ _ (tensorRight (Q.X n))) ∧ _
  refine ⟨fun n ↦ (hQf n).2, hQc, hQz, ?_, ?_, ?_, ?_, ?_⟩
  · exact CochainComplex.kFlat_of_bounded_of_flat Q (a - r) (b - r) hQf
  · let P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ :=
      ((upperStar (ModuleCat.{u + 1} R) f).mapHomologicalComplex (.up ℤ)).obj C
    have : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).2 fun n hn ↦
      (upperStar (ModuleCat.{u + 1} R) f).map_isZero (_hz n (.inr hn))
    have hPf (n : ℤ) : ObjectProperty.flat (P.X n) := by
      change ObjectProperty.flat ((upperStar (ModuleCat.{u + 1} R) f).obj (C.X n))
      exact Functor.PreservesFlat.flat_obj (F := upperStar (ModuleCat.{u + 1} R) f) (hCf n)
    have hPk := CochainComplex.kFlat_of_isStrictlyLE_of_flat P b hPf
    have : IsIso (etalePullbackRepresentative R f C K e) := by
      dsimp only [etalePullbackRepresentative]
      infer_instance
    exact line_comparison_isIso P _ (etalePullbackRepresentative R f C K e) E r hPk
  · intro n
    have (i : ℤ) : Scheme.IsConstructibleSheaf (Q.X i) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hQc i)
    let T := Q.sc n
    have : Scheme.IsConstructibleSheaf T.X₁ := inferInstanceAs
      (Scheme.IsConstructibleSheaf (Q.X _))
    have : Scheme.IsConstructibleSheaf T.X₂ := inferInstanceAs
      (Scheme.IsConstructibleSheaf (Q.X _))
    have : Scheme.IsConstructibleSheaf T.X₃ := inferInstanceAs
      (Scheme.IsConstructibleSheaf (Q.X _))
    have := Scheme.IsConstructibleSheaf.kernel T.g
    have : Scheme.IsConstructibleSheaf T.cycles :=
      Scheme.IsConstructibleSheaf.of_iso (F := kernel T.g)
        (T.cyclesIsKernel.conePointUniqueUpToIso (kernelIsKernel T.g)).symm
    have := Scheme.IsConstructibleSheaf.cokernel T.toCycles
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (Scheme.IsConstructibleSheaf.of_iso (F := cokernel T.toCycles)
        ((cokernelIsCokernel T.toCycles).coconePointUniqueUpToIso T.homologyIsCokernel))
  · intro N n hn
    have ht := _root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat Q (a - r) (b - r) hQf N
    rcases hn with hn | hn
    · exact (_root_.DerivedCategory.isGE_iff _ (a - r)).1 ht.1 n hn
    · exact (_root_.DerivedCategory.isLE_iff _ (b - r)).1 ht.2 n hn
  · intro j S d M _hM hd k
    let A := ModuleCat.{u + 1} R
    let Z := (S.pullback f).domain k
    let g : Z ⟶ S.domain k := pullback.fst (S.immersion k) f
    let z : Z ⟶ X := (S.pullback f).immersion k
    let G := (upperStar A (S.immersion k)).obj (C.homology (j + r))
    let P : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ :=
      ((upperStar A f).mapHomologicalComplex (.up ℤ)).obj C
    let T : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ :=
      ((tensorRight E).mapHomologicalComplex (.up ℤ)).obj P
    have := hEf.tensorRight.preservesFiniteLimits
    have := hEf.tensorRight.preservesFiniteColimits
    have eH : Q.homology j ≅ (upperStar A f).obj (C.homology (j + r)) ⊗ E :=
      ((HomologicalComplex.homologyFunctor _ (.up ℤ) 0).shiftIso r j (j + r)
        (by omega)).app T ≪≫
      (P.sc (j + r)).mapHomologyIso (tensorRight E) ≪≫
      (tensorRight E).mapIso ((C.sc (j + r)).mapHomologyIso (upperStar A f))
    have ebase : (upperStar A z).obj ((upperStar A f).obj (C.homology (j + r))) ≅
        (upperStar A g).obj G :=
      ((upperStarComp A z f).app _).symm ≪≫
      eqToIso (congrArg (fun q ↦ (upperStar A q).obj (C.homology (j + r)))
        (show z ≫ f = g ≫ S.immersion k from pullback.condition.symm)) ≪≫
      (upperStarComp A g (S.immersion k)).app _
    have eStr : (upperStar A z).obj (Q.homology j) ≅
        (upperStar A g).obj G ⊗ (upperStar A z).obj E :=
      (upperStar A z).mapIso eH ≪≫
      (Functor.Monoidal.μIso (upperStar A z) _ E).symm ≪≫
      tensorIso ebase (Iso.refl _)
    refine ⟨⟨eStr⟩, fun i ↦ ?_⟩
    let U := (d k).cover
    let W := etalePullbackLineCover f S k U V
    let h : W.X i ⟶ Z := W.f i
    let l : W.X i ⟶ U.X i.1 :=
      pullback.fst ((U.pullback₂ g).f i.1) ((V.pullback₂ z).f i.2) ≫
        pullback.fst (U.f i.1) g
    let q : W.X i ⟶ V.X i.2 :=
      pullback.snd ((U.pullback₂ g).f i.1) ((V.pullback₂ z).f i.2) ≫
        pullback.fst (V.f i.2) z
    have hl : h ≫ g = l ≫ U.f i.1 := by
      change (pullback.fst _ _ ≫ pullback.snd (U.f i.1) g) ≫ g =
        (pullback.fst _ _ ≫ pullback.fst (U.f i.1) g) ≫ U.f i.1
      simp only [Category.assoc, pullback.condition]
    have hq : h ≫ z = q ≫ V.f i.2 := by
      change (pullback.fst ((U.pullback₂ g).f i.1) ((V.pullback₂ z).f i.2) ≫
        (U.pullback₂ g).f i.1) ≫ z =
        (pullback.snd _ _ ≫ pullback.fst (V.f i.2) z) ≫ V.f i.2
      rw [pullback.condition]
      simp only [Category.assoc, pullback.condition]
      rfl
    let equiv := Scheme.Etale.overSheafEquiv (U.etalePrecoverageToEtale i.1) A
    have eU : (upperStar A (U.f i.1)).obj G ≅
        (constantSheaf (U.X i.1).smallEtaleTopology A).obj (M k i.1) :=
      (Scheme.overSheafEquivFunctorObjOverIso A (U.etalePrecoverageToEtale i.1) G).symm ≪≫
      equiv.functor.mapIso (hd k i.1).some ≪≫
      ((Scheme.Etale.overEquiv (U.etalePrecoverageToEtale i.1)).constantSheafSheafCongrIso
        _ _ A Over.mkIdTerminal).app (M k i.1)
    have e₁ : (upperStar A h).obj ((upperStar A g).obj G) ≅
        (constantSheaf (W.X i).smallEtaleTopology A).obj (M k i.1) :=
      ((upperStarComp A h g).app G).symm ≪≫
      eqToIso (congrArg (fun m ↦ (upperStar A m).obj G) hl) ≪≫
      (upperStarComp A l (U.f i.1)).app G ≪≫
      (upperStar A l).mapIso eU ≪≫
      (Scheme.upperStarConstantSheafIso A l).app (M k i.1)
    have e₂ : (upperStar A h).obj ((upperStar A z).obj E) ≅
        (constantSheaf (W.X i).smallEtaleTopology A).obj (ModuleCat.of R R) :=
      ((upperStarComp A h z).app E).symm ≪≫
      eqToIso (congrArg (fun m ↦ (upperStar A m).obj E) hq) ≪≫
      (upperStarComp A q (V.f i.2)).app E ≪≫
      (upperStar A q).mapIso (_hE i.2).some ≪≫
      (Scheme.upperStarConstantSheafIso A q).app (ModuleCat.of R R)
    exact ⟨(upperStar A h).mapIso eStr ≪≫
      (Functor.Monoidal.μIso (upperStar A h) _ _).symm ≪≫
      tensorIso e₁ e₂ ≪≫
      Functor.Monoidal.μIso (constantSheaf (W.X i).smallEtaleTopology A) _ _ ≪≫
      (constantSheaf (W.X i).smallEtaleTopology A).mapIso (ρ_ (M k i.1))⟩

end AlgebraicGeometry.Etale
