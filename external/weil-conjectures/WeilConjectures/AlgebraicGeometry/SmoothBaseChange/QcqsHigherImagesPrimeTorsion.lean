/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit

/-!
# Qcqs higher direct images preserve a fixed set of torsion primes

Source: Stacks Project, Tags 0DDD (1) and 0DDC (1), fixed-prime refinement
(blueprint: lem-sbc-qcqs-higher-images-prime-torsion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The small divisibility index for the restricted kernel union in Stacks Tag 0DDC.
The integer 1 is allowed even when P has no prime members. -/
private structure PrimeAnnihilator (P : Set ℕ) where
  val : ℕ
  pos : 0 < val
  allowed : ∀ p : ℕ, p.Prime → p ∣ val → p ∈ P

private instance (P : Set ℕ) : PartialOrder (PrimeAnnihilator P) where
  le n m := n.val ∣ m.val
  lt n m := n.val ∣ m.val ∧ ¬m.val ∣ n.val
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl n := dvd_refl n.val
  le_trans _ _ _ := dvd_trans
  le_antisymm n m hnm hmn := by
    cases n
    cases m
    congr
    exact Nat.dvd_antisymm hnm hmn

/-- The restricted kernel union from Stacks Tags 0DDC and 0DDD, followed by an
additive functor preserving small filtered colimits. The colimit map is mono by AB5.
Its epimorphism property follows by lifting each geometric-stalk element through
its annihilator kernel and using geometric-stalk joint faithfulness. A colimit
representative then retains the kernel's allowed annihilator under the functor. -/
private theorem prime_torsion_of_filtered_functor
    {X : Scheme.{u}} (P : Set ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
      (x : ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F),
      ∃ n : ℕ, 0 < n ∧ n • x = 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ∈ P)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1})
    [H.Additive] [PreservesFilteredColimitsOfSize.{0, 0} H]
    (y : H.obj F) :
    ∃ m : ℕ, 0 < m ∧ m • y = 0 ∧ ∀ p : ℕ, p.Prime → p ∣ m → p ∈ P := by
  classical
  let I := PrimeAnnihilator P
  have : Nonempty I := ⟨⟨1, Nat.zero_lt_one, fun p hp h ↦
    (hp.not_dvd_one h).elim⟩⟩
  have : IsDirected I (· ≤ ·) := ⟨fun n m ↦ by
    refine ⟨⟨n.val * m.val, mul_pos n.pos m.pos, ?_⟩,
      dvd_mul_right n.val m.val, dvd_mul_left m.val n.val⟩
    intro p hp hpm
    rcases hp.dvd_mul.mp hpm with hn | hm
    · exact n.allowed p hp hn
    · exact m.allowed p hp hm⟩
  have : IsFiltered I := inferInstance
  have : IsConnected I := IsFiltered.isConnected I
  have : HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{0, 0}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  have : AB5OfSize.{0, 0}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    AB5OfSize_of_univLE.{0, 0, u + 1, u + 1} _
  have hN : Monotone fun n : I ↦ kernelSubobject (n.val • 𝟙 F) := by
    intro n m hnm
    obtain ⟨r, hr⟩ := (show n.val ∣ m.val from hnm)
    have he : m.val • 𝟙 F = (n.val • 𝟙 F) ≫ (r • 𝟙 F) := by
      simp only [hr, Preadditive.comp_nsmul, Category.comp_id, mul_comm, mul_nsmul]
      exact smul_comm _ _ _
    change kernelSubobject _ ≤ kernelSubobject _
    rw [he]
    exact kernelSubobject_comp_le _ _
  let D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    hN.functor ⋙ Subobject.underlying
  let α : D ⟶ (Functor.const I).obj F :=
    { app := fun n ↦ (kernelSubobject (n.val • 𝟙 F)).arrow
      naturality := by intro n m h; simp [D] }
  have : ∀ n, Mono (α.app n) := fun n ↦ inferInstanceAs (Mono (Subobject.arrow _))
  have : Mono α := NatTrans.mono_of_mono_app α
  have : HasColimitsOfShape I
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    HasColimitsOfSize.has_colimits_of_shape.{0, 0} I
  have : HasColimit D := HasColimitsOfShape.has_colimit D
  let c : Cocone D := ⟨F, α⟩
  let t := colimit.desc D c
  have : Mono t := colim.map_mono' α (colimit.isColimit D) (isColimitConstCocone I F) t
    (fun n ↦ (colimit.ι_desc _ _).trans (Category.comp_id _).symm)
  have : Epi t := by
    refine ⟨fun {G} g h hgh ↦ ?_⟩
    have hk (n : I) : α.app n ≫ g = α.app n ≫ h := by
      simpa [t, c] using colimit.ι D n ≫= hgh
    have : HasLimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
      hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
    have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
      AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
    apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
    intro p
    let T := (Scheme.pointSmallEtale (X.algClosurePoint p)).sheafFiber
      (A := AddCommGrpCat.{u + 1})
    have : T.Additive := (Scheme.pointSmallEtale (X.algClosurePoint p)).sheafFiber_additive
    ext x
    obtain ⟨n, hn, hx, hnp⟩ := hF _ (X.algClosurePoint p) x
    have : LocallySmall.{u} X.Etale := ⟨fun _ _ ↦ small_self _⟩
    have : PreservesFiniteLimits T := inferInstance
    have hS := (ShortComplex.kernelSequence_exact (n • 𝟙 F)).map_of_mono_of_preservesKernel
      T inferInstance inferInstance
    have hx' : T.map (n • 𝟙 F) x = 0 := by
      simpa only [Functor.map_nsmul, T.map_id, AddCommGrpCat.hom_nsmul,
        AddMonoidHom.nsmul_apply, AddCommGrpCat.id_apply] using hx
    obtain ⟨z, hz⟩ := (ShortComplex.ab_exact_iff _).1 hS x hx'
    have he : kernel.ι (n • 𝟙 F) ≫ g = kernel.ι (n • 𝟙 F) ≫ h := by
      rw [← kernelSubobject_arrow', Category.assoc, Category.assoc]
      exact (kernelSubobjectIso _).inv ≫= hk ⟨n, hn, hnp⟩
    have he' := congr(T.map $he z)
    simp only [Functor.map_comp] at he'
    rw [← hz]
    exact he'
  have : IsIso t := isIso_of_mono_of_epi t
  have : IsIso ((colimit.isColimit D).desc c) := show IsIso t from inferInstance
  have hc : IsColimit c := IsColimit.ofPointIso (colimit.isColimit D)
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{0, u + 1, 0, u + 1} _
  have hH : IsColimit (H.mapCocone c) := isColimitOfPreserves H hc
  obtain ⟨n, z, rfl⟩ := Concrete.isColimit_exists_rep _ hH y
  refine ⟨n.val, n.pos, ?_, n.allowed⟩
  have hn : n.val • 𝟙 (D.obj n) = 0 := by
    rw [← cancel_mono (α.app n), Preadditive.nsmul_comp, Category.id_comp, zero_comp]
    have he := kernelSubobject_arrow_comp (n.val • 𝟙 F)
    rw [Preadditive.comp_nsmul, Category.comp_id] at he
    exact he
  have hnH : n.val • 𝟙 (H.obj (D.obj n)) = 0 := by
    rw [← H.map_id, ← H.map_nsmul, hn, H.map_zero]
  have hz : n.val • z = 0 := by
    exact ConcreteCategory.congr_hom hnH z
  change n.val • (H.map (α.app n)) z = 0
  rw [← map_nsmul, hz, map_zero]

/-- Integer-module coefficients carry precisely the data of an abelian sheaf.
Use Mathlib's ring-equivalence restriction of scalars and integer-module equivalence,
then restrict the coefficient adjunction along the full sheaf subcategories. -/
private theorem integerSheafForget_isEquivalence (X : Scheme.{u}) :
    (moduleAbelianForget (ULift.{u + 1} ℤ) X).IsEquivalence := by
  let E := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}
  have : E.IsEquivalence := by
    change (ModuleCat.restrictScalars
      (ULift.ringEquiv.symm : ℤ ≃+* ULift.{u + 1} ℤ).toRingHom ⋙
        forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsEquivalence
    infer_instance
  let a := (E.adjunction.whiskerRight X.Etaleᵒᵖ).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (fullyFaithfulSheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (L := sheafCompose X.smallEtaleTopology E)
    (R := sheafCompose X.smallEtaleTopology E.inv) (Iso.refl _) (Iso.refl _)
  exact a.toEquivalence.isEquivalence_functor

/-- Higher direct images along a quasi-compact quasi-separated scheme morphism preserve
stalkwise torsion whose annihilators have prime divisors in a fixed set `P`.
Only prime members of `P : Set ℕ` are tested, so this encodes an arbitrary set of primes.
Source: Stacks Project, Tags 0DDD (1) and 0DDC (1), fixed-prime refinement.
(blueprint: lem-sbc-qcqs-higher-images-prime-torsion)

Proof:
1. Take an affine pointed etale neighbourhood W of the target geometric point. The scheme Z = U
×_V W is qcqs by lem-weil-pbc-qcqs-morphism-permanence and lem-weil-pbc-qcqs-over-affine. Its
pulled-back sheaf G has the same allowed-prime stalk torsion by lemma-openclosed-stalk-upperstar.
No global qcqs condition on U or V is needed.

2. Order the positive integers with prime divisors in P by divisibility. This is a nonempty
directed set (1 is an index and nm bounds n and m). Form G[n] = ker(n : G → G) using
def-pur-abelian-sheaf-kernel. Divisibility gives inclusions and a cocone to G. The colimit C
exists by lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact; the indices form a subset of
the natural numbers.

3. The map C → G is an isomorphism on stalks: prop-weil-pbc-geometric-stalks-exact identifies
stalks of G[n] with kernels and definition-torsion-sheaves--3 identifies stalks of C with their
colimit. The hypothesis supplies surjectivity. Represent a colimit element by a kernel element
using lem-weil-pbc-filtered-colimit-modules-elementwise over the integers; if it maps to zero,
the representative is zero by the subgroup inclusion. Thus the stalk map is bijective. Apply
lemma-weil-pbc-geometric-stalk-conservative to conclude that G is the colimit of G[n] with the
actual inclusion maps.

4. Apply lem-weil-pbc-etale-directed-cohomology-colimit on Z to this directed diagram. Every
cohomology class of G comes from H^q(Z, G[n]) for some allowed n, by
lem-weil-pbc-filtered-colimit-modules-elementwise over the integers. There is no uniform
annihilator assumption.

5. Sectionwise kernels give n id of G[n] equal to zero. Cohomology is the right derived sections
functor by def-weil-pbc-sites-and-cohomology, and its degree functors are additive by
lem-weil-pbc-right-derived-universal-delta-functor. Hence n kills H^q(Z, G[n]); the
inclusion-induced group homomorphism shows that n kills the represented class in H^q(Z, G).

6. Use proposition-base-change-larger-algebraically-closed and definition-torsion-sheaves--3 to
express the target stalk as the filtered colimit of cohomology over pointed etale neighbourhoods.
The index is filtered by definition-torsion-sheaves--3. Use
lem-weil-pbc-filtered-colimit-modules-elementwise to represent the chosen stalk element on a
neighbourhood; lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink refines it to an affine one
without changing the stalk class. Work in a common universe, or a small equivalent index
category.

7. Apply steps 1–5 to this affine representative. The map to the stalk is a group homomorphism,
so its positive allowed-prime annihilator also kills the original stalk element. This works for
every nonnegative degree and every target geometric point. -/
theorem qcqs_higherDirectImages_prime_torsion
    {U V : Scheme.{u}} (f : U ⟶ V) [QuasiCompact f] [QuasiSeparated f]
    (P : Set ℕ) (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U)
      (x : (((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F)),
      ∃ n : ℕ, 0 < n ∧ n • x = 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ∈ P)
    (q : ℕ) (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ V)
    (y : (((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))))) :
    ∃ m : ℕ, 0 < m ∧ m • y = 0 ∧ ∀ p : ℕ, p.Prime → p ∣ m → p ∈ P := by
  classical
  -- Transfer through the integer-module sheaf equivalence.
  let Λ := ULift.{u + 1} ℤ
  let A := moduleAbelianForget Λ U
  let B := moduleAbelianForget Λ V
  have : A.IsEquivalence := integerSheafForget_isEquivalence U
  have : B.IsEquivalence := integerSheafForget_isEquivalence V
  let M := DerivedCategory.Plus.singleFunctor
    (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ (q : ℤ)
  let T := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
  let H := A.inv ⋙ M ⋙ B ⋙ T
  have : A.Additive := inferInstance
  have : A.inv.Additive := inferInstance
  have : M.Additive := inferInstance
  have : B.Additive := inferInstance
  have : T.Additive := (Scheme.pointSmallEtale s).sheafFiber_additive
  have : H.Additive := inferInstance
  have hM (J : Type) [SmallCategory J] [IsFiltered J] :
      PreservesColimitsOfShape J M :=
    preservesColimitsOfShape_higherDirectImage Λ f (q : ℤ) J
  have : PreservesFilteredColimitsOfSize.{0, 0} H := by
    constructor
    intro J _ _
    have : PreservesColimitsOfShape J M := hM J
    dsimp only [H]
    infer_instance
  let G := DerivedCategory.Plus.singleFunctor
    (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
      rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f ⋙
        DerivedCategory.Plus.homologyFunctor _ (q : ℤ)
  -- Identify the converted functor's value with the exact stalk in the statement.
  obtain ⟨e⟩ := nonempty_higherDirectImage_forget_iso Λ f (q : ℤ) (A.inv.obj F)
  let e' : B.obj (M.obj (A.inv.obj F)) ≅ G.obj F :=
    e ≪≫ G.mapIso (A.asEquivalence.counitIso.app F)
  let e'' : H.obj F ≅ T.obj (G.obj F) := T.mapIso e'
  obtain ⟨n, hn, hx, hnp⟩ :=
    prime_torsion_of_filtered_functor P F hF H (e''.inv y)
  refine ⟨n, hn, ?_, hnp⟩
  have he := congrArg e''.hom hx
  simpa only [map_nsmul, map_zero, Iso.inv_hom_id_apply] using he

end AlgebraicGeometry.Etale
