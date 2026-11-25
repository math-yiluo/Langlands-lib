/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleOfFiniteCoefficientSets
import WeilConjectures.AlgebraicGeometry.ConstructibleUnderlyingSetsOfFiniteStalks
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientOfFiniteStalks
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison
import WeilConjectures.AlgebraicGeometry.Curve.FiniteCoefficientAssertions
import WeilConjectures.AlgebraicGeometry.KilledSheafModuleLift
import WeilConjectures.AlgebraicGeometry.TorsionKernelCohomology
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# The curve assertions `C₃`–`C₆` for torsion coefficients

Let `k` be an algebraically closed field and `C` a curve over `k` (`AlgebraicGeometry.IsCurve`).
This file proves the assertions `C₃`, `C₄`, `C₅` and `C₆` of the cohomology of curves:

3. `Hᵠ(C, F) = 0` for `q ≥ 2` if `char k = p > 0` and `F` is `p`-primary torsion;
4. `Hᵠ(C, F)` is finite if `F` is constructible with finite stalks and torsion prime to
   `char k`;
5. `Hᵠ(C, F)` is finite if `C` is proper and `F` is constructible with finite stalks;
6. the pullback `Hᵠ(C, F) ⟶ Hᵠ(C_{k'}, F|)` is bijective for every algebraically closed
   extension `k'/k` if the torsion of `F` is prime to `char k`.

The coefficient sheaves are sheaves of `Λ`-modules over an arbitrary ring `Λ` and the cohomology
is that of the underlying abelian sheaf, as in `AlgebraicGeometry.IsCurve.Assertions`.

## Main statements

- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_two_le_of_isPrimaryTorsionSheaf`: `C₃`.
- `AlgebraicGeometry.IsCurve.finite_sheafH_of_isTorsionSheafOfInvertibleOrder`: `C₄`.
- `AlgebraicGeometry.IsCurve.finite_sheafH_of_isProper`: `C₅`.
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder`: `C₆`.

## Implementation details

All four assertions are deduced from the finite-coefficient case
`AlgebraicGeometry.IsCurve.Assertions.of_finite_coefficients`. For `C₄` and `C₅` the sections
of `F` are killed by an ideal `I` of `Λ` with `Λ ⧸ I` finite
(`AlgebraicGeometry.Scheme.finite_quotient_section_annihilator_of_finite_stalks`), hence by the
characteristic `N > 0` of `Λ ⧸ I`, so that the underlying abelian sheaf of `F` is that of a
constructible sheaf of `ℤ/N`-modules. For `C₃` and `C₆` the sheaf `F` may have unbounded
torsion; they are deduced by writing the underlying abelian sheaf `A` of `F` as the filtered
colimit of its subsheaves `A[n]`
(`AlgebraicGeometry.Scheme.subsingleton_sheafH_of_forall_torsionBy`,
`AlgebraicGeometry.Etale.bijective_cohomologyMap_of_forall_torsionBy`): each `A[n]` is a sheaf
of `ℤ/n`-modules (`AlgebraicGeometry.exists_module_sheaf_of_nsmul_id_eq_zero`), and its
geometric stalks embed into those of `F`.

## References

- Stacks Project, Theorem 59.83.1, <https://stacks.math.columbia.edu/tag/03SC>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsCurve

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- A monomorphism between the underlying abelian sheaves of a sheaf of `R`-modules `G` and a
sheaf of `Λ`-modules `F` embeds every geometric stalk of `G` into that of `F`. -/
private theorem exists_injective_sheafFiber_of_mono {R : Type (u + 1)} [CommRing R]
    {X : Scheme.{u}} {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (m : (sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj G ⟶
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) [Mono m]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    ∃ φ : ↥(((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} R)).obj G) →+
      ↥(((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F),
      Function.Injective φ := by
  have : LocallySmall.{u} X.Etale := locallySmall_self _
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let Φ := Scheme.pointSmallEtale s
  let eR := (Φ.sheafFiberCompIso (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).app G
  let eΛ := (Φ.sheafFiberCompIso (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app F
  let E := Φ.sheafFiber (A := AddCommGrpCat.{u + 1})
  have : PreservesFiniteLimits E := inferInstance
  have : E.PreservesMonomorphisms := preservesMonomorphisms_of_preservesLimitsOfShape E
  have : Mono (eR.inv ≫ E.map m ≫ eΛ.hom) := inferInstance
  exact ⟨(eR.inv ≫ E.map m ≫ eΛ.hom).hom, (AddCommGrpCat.mono_iff_injective _).mp this⟩

/-- `p`-primary torsion passes to a sheaf whose underlying abelian sheaf embeds into that of a
`p`-primary torsion sheaf. -/
private theorem isPrimaryTorsionSheaf_of_mono {R : Type (u + 1)} [CommRing R]
    {X : Scheme.{u}} {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (m : (sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj G ⟶
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) [Mono m]
    (p : ℕ) (hF : Scheme.IsPrimaryTorsionSheaf Λ F p) : Scheme.IsPrimaryTorsionSheaf R G p := by
  intro Ω _ _ s x
  obtain ⟨φ, hφ⟩ := exists_injective_sheafFiber_of_mono m Ω s
  obtain ⟨n, hn⟩ := hF Ω s (φ x)
  exact ⟨n, hφ (by rw [map_nsmul, hn, map_zero])⟩

/-- Torsion of orders invertible on `S` passes to a sheaf whose underlying abelian sheaf embeds
into that of such a sheaf. -/
private theorem isTorsionSheafOfInvertibleOrder_of_mono {R : Type (u + 1)} [CommRing R]
    {X : Scheme.{u}} (S : Scheme.{u}) {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (m : (sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj G ⟶
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) [Mono m]
    [Scheme.IsTorsionSheafOfInvertibleOrder S F] : Scheme.IsTorsionSheafOfInvertibleOrder S G := by
  constructor
  intro Ω _ _ s x
  obtain ⟨φ, hφ⟩ := exists_injective_sheafFiber_of_mono m Ω s
  obtain ⟨n, hn, hu, hx⟩ :=
    Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero (S := S) Ω s (φ x)
  exact ⟨n, hn, hu, hφ (by rw [map_nsmul, hx, map_zero])⟩

/-- Bijectivity of a pullback map on cohomology is invariant under isomorphisms of the
coefficient sheaf. -/
private theorem bijective_cohomologyMap_of_iso {X Y : Scheme.{u}} (a : Y ⟶ X)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (q : ℕ)
    (h : Function.Bijective (Etale.cohomologyMap a F q)) :
    Function.Bijective (Etale.cohomologyMap a G q) := by
  let eX := ((Sheaf.functorH X.smallEtaleTopology q).mapIso e).addCommGroupIsoToAddEquiv
  let eY := ((Sheaf.functorH Y.smallEtaleTopology q).mapIso
    ((Etale.upperStar _ a).mapIso e)).addCommGroupIsoToAddEquiv
  have heq : ⇑(Etale.cohomologyMap a G q) = eY ∘ Etale.cohomologyMap a F q ∘ eX.symm := by
    funext x
    change Etale.cohomologyMap a G q x =
      Sheaf.H.map ((Etale.upperStar _ a).map e.hom) q
        (Etale.cohomologyMap a F q (Sheaf.H.map e.inv q x))
    rw [← Etale.cohomologyMap_map, ← Sheaf.H.map_comp_apply, e.inv_hom_id]
    simp
  rw [heq]
  exact eY.bijective.comp (h.comp eX.symm.bijective)

/-- The `n`-torsion subsheaf of the underlying abelian sheaf of `F` is the underlying abelian
sheaf of a sheaf `M` of `ℤ/n`-modules for which the eight assertions hold. -/
private theorem exists_assertions_torsionBy {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ+) :
    ∃ (M : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))))
      (_ : (sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
        AddCommGrpCat.{u + 1})).obj M ≅ Scheme.torsionBy
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) n),
      IsCurve.Assertions (ULift.{u + 1} (ZMod n)) f M := by
  obtain ⟨M, ⟨e⟩⟩ := exists_module_sheaf_of_nsmul_id_eq_zero C n _
    (Scheme.torsionBy_nsmul_id _ n)
  exact ⟨M, e, Assertions.of_finite_coefficients _ f M⟩

/-- **Assertion `C₃` of the cohomology of curves.** Let `k` be an algebraically closed field of
characteristic `p > 0`, `C` a curve over `k` and `F` a `p`-primary torsion sheaf of
`Λ`-modules on `C_ét`. Then `Hᵠ(C, F) = 0` for every `q ≥ 2`. -/
theorem subsingleton_sheafH_of_two_le_of_isPrimaryTorsionSheaf {k : Type u} [Field k]
    [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (p : ℕ) [Fact p.Prime] [CharP k p]
    (hF : Scheme.IsPrimaryTorsionSheaf Λ F p) (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) := by
  have : CompactSpace C := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated f
  have : Scheme.IsTorsionModuleSheaf F := ⟨fun Ω _ _ s x ↦ by
    obtain ⟨m, hm⟩ := hF Ω s x
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2
      ⟨p ^ m, pow_pos (Fact.out : p.Prime).pos m, hm⟩⟩
  have hA := (Scheme.isTorsionAbelianSheaf_characterizations _).1.mpr
    ((Scheme.isTorsionModuleSheaf_iff_isTorsion F).mp inferInstance)
  refine Scheme.subsingleton_sheafH_of_forall_torsionBy _ hA q fun n ↦ ?_
  obtain ⟨M, e, hM⟩ := exists_assertions_torsionBy f F n
  have : Subsingleton ((Sheaf.functorH C.smallEtaleTopology q).obj _) :=
    hM.subsingleton_of_one_lt_of_isPrimaryTorsionSheaf p
      (isPrimaryTorsionSheaf_of_mono (e.hom ≫ kernel.ι _) p hF) q hq
  exact ((Sheaf.functorH _ q).mapIso e).addCommGroupIsoToAddEquiv.symm.injective.subsingleton

/-- Constructibility of an étale sheaf of sets is invariant under isomorphisms. -/
private theorem isConstructibleEtaleSheafOfSets_of_iso {X : Scheme.{u}}
    {G H : Sheaf X.smallEtaleTopology (Type (u + 1))} (e : G ≅ H)
    (hG : Scheme.IsConstructibleEtaleSheafOfSets G) :
    Scheme.IsConstructibleEtaleSheafOfSets H := by
  obtain ⟨S, hS⟩ := hG
  refine ⟨S, fun i ↦ ?_⟩
  obtain ⟨⟨𝒰, h𝒰⟩, hfin⟩ := hS i
  let e' := (Scheme.etaleSetPullback (S.immersion i)).mapIso e
  refine ⟨⟨𝒰, fun j ↦ ?_⟩,
    Scheme.isFiniteSheaf_of_finite_algClosed_stalks _ fun Ω _ _ s ↦ ?_⟩
  · have := h𝒰 j
    exact Sheaf.isConstant_congr _
      (((S.domain i).smallEtaleTopology.overPullback (Type (u + 1)) _).mapIso e')
  · exact @Finite.of_equiv _ _ ((ConcreteCategory.isFinitelyGenerated_iff_finite _).mp
        (hfin.isFinitelyGenerated_sheafFiber Ω s))
      ((Scheme.pointSmallEtale s).sheafFiber.mapIso e').toEquiv

/-- A constructible sheaf `F` of `Λ`-modules with finite geometric stalks on a curve has the
same underlying abelian sheaf as a constructible sheaf `M` of `ℤ/N`-modules for some `N > 0`. -/
private theorem exists_finite_coefficients_of_finite_stalks {k : Type u} [Field k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsConstructibleSheaf F]
    (hfin : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ C),
      Finite ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj F)) :
    ∃ (N : ℕ) (_ : NeZero N)
      (M : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))))
      (_ : (sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N)))
        AddCommGrpCat.{u + 1})).obj M ≅
          (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F),
      Scheme.IsConstructibleSheaf M := by
  have : IsNoetherian C := isNoetherian_of_locallyOfFiniteType f
  let I : Ideal Λ := ⨅ U : C.Etaleᵒᵖ, Module.annihilator Λ (F.obj.obj U)
  have : Finite (Λ ⧸ I) :=
    Scheme.finite_quotient_section_annihilator_of_finite_stalks Λ F inferInstance hfin
  let N := ringChar (Λ ⧸ I)
  have hN : NeZero N := ⟨CharP.char_ne_zero_of_finite (Λ ⧸ I) N⟩
  have hNI : (N : Λ) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  have hkill : N • 𝟙 ((sheafCompose _
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) = 0 := by
    ext U x
    have h := Module.mem_annihilator.mp (Ideal.mem_iInf.mp hNI U) x
    rw [Nat.cast_smul_eq_nsmul] at h
    exact h
  obtain ⟨M, ⟨e⟩⟩ := exists_module_sheaf_of_nsmul_id_eq_zero C N _ hkill
  refine ⟨N, hN, M, e, ?_⟩
  refine Scheme.isConstructibleSheaf_of_finite_coefficient_underlying_sets _ M
    (isConstructibleEtaleSheafOfSets_of_iso
      ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso e.symm)
      (Scheme.isConstructibleEtaleSheafOfSets_of_finite_module_stalks Λ F inferInstance hfin))
    ⊥ (Finite.of_surjective _ Ideal.Quotient.mk_surjective) fun U r hr m ↦ ?_
  rw [Ideal.mem_bot.mp hr, zero_smul]

/-- **Assertion `C₄` of the cohomology of curves.** Let `k` be an algebraically closed field,
`C` a curve over `k` and `F` a constructible sheaf of `Λ`-modules on `C_ét` with finite
geometric stalks whose torsion is prime to `char k`. Then every `Hᵠ(C, F)` is finite. -/
theorem finite_sheafH_of_isTorsionSheafOfInvertibleOrder {k : Type u} [Field k]
    [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsConstructibleSheaf F]
    (hfin : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ C),
      Finite ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj F))
    [Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F] (q : ℕ) :
    Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) := by
  obtain ⟨N, _, M, e, _⟩ := exists_finite_coefficients_of_finite_stalks f F hfin
  have := isTorsionSheafOfInvertibleOrder_of_mono (Spec (.of k)) e.hom (F := F)
  have hM := (Assertions.of_finite_coefficients _ f M).finite_of_isTorsionSheafOfInvertibleOrder q
  exact @Finite.of_equiv _ _ hM ((Sheaf.functorH _ q).mapIso e).addCommGroupIsoToAddEquiv.toEquiv

/-- **Assertion `C₅` of the cohomology of curves.** Let `k` be an algebraically closed field,
`C` a proper curve over `k` and `F` a constructible sheaf of `Λ`-modules on `C_ét` with finite
geometric stalks. Then every `Hᵠ(C, F)` is finite. -/
theorem finite_sheafH_of_isProper {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f]
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsConstructibleSheaf F]
    (hfin : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ C),
      Finite ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj F))
    (q : ℕ) :
    Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) := by
  obtain ⟨N, _, M, e, _⟩ := exists_finite_coefficients_of_finite_stalks f F hfin
  have hM := (Assertions.of_finite_coefficients _ f M).finite_of_isProper q
  exact @Finite.of_equiv _ _ hM ((Sheaf.functorH _ q).mapIso e).addCommGroupIsoToAddEquiv.toEquiv

/-- `C₄` for a finite coefficient ring `Λ`, where constructible sheaves have finite stalks. -/
theorem finite_sheafH_of_isTorsionSheafOfInvertibleOrder_of_finite [Finite Λ] {k : Type u}
    [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsConstructibleSheaf F]
    [Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F] (q : ℕ) :
    Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) :=
  (Assertions.of_finite_coefficients Λ f F).finite_of_isTorsionSheafOfInvertibleOrder q

/-- `C₅` for a finite coefficient ring `Λ`, where constructible sheaves have finite stalks. -/
theorem finite_sheafH_of_isProper_of_finite [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f]
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsConstructibleSheaf F]
    (q : ℕ) :
    Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) :=
  (Assertions.of_finite_coefficients Λ f F).finite_of_isProper q

/-- **Assertion `C₆` of the cohomology of curves.** Let `k ⊆ k'` be algebraically closed fields,
`C` a curve over `k` and `F` a torsion sheaf of `Λ`-modules on `C_ét` whose torsion is prime to
`char k`. For every cartesian square

```
C' --ι'--> C
|          |
f'         f
v          v
Spec k' -ι-> Spec k
```

the pullback map `Hᵠ(C, F) ⟶ Hᵠ(C', ι'^* F)` on the cohomology of the underlying abelian
sheaves is bijective for every `q`. -/
theorem bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder {k k' : Type u} [Field k]
    [IsAlgClosed k] [Field k'] [IsAlgClosed k'] {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsCurve f] {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) := by
  have : CompactSpace C := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated f
  have : QuasiCompact f' := MorphismProperty.of_isPullback h inferInstance
  have : IsSeparated f' := MorphismProperty.of_isPullback h inferInstance
  have : CompactSpace C' := (quasiCompact_iff_compactSpace f').mp inferInstance
  have : QuasiSeparatedSpace C' := quasiSeparatedSpace_of_quasiSeparated f'
  have : Scheme.IsTorsionModuleSheaf F :=
    Scheme.IsTorsionModuleSheaf.of_isTorsionSheafOfInvertibleOrder (Spec (.of k)) F
  have hA := (Scheme.isTorsionAbelianSheaf_characterizations _).1.mpr
    ((Scheme.isTorsionModuleSheaf_iff_isTorsion F).mp inferInstance)
  refine Etale.bijective_cohomologyMap_of_forall_torsionBy ι' _ hA q fun n ↦ ?_
  obtain ⟨M, e, hM⟩ := exists_assertions_torsionBy f F n
  have := isTorsionSheafOfInvertibleOrder_of_mono (Spec (.of k)) (e.hom ≫ kernel.ι _) (F := F)
  exact bijective_cohomologyMap_of_iso ι' e _
    (hM.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder k' h q)

end AlgebraicGeometry.IsCurve
