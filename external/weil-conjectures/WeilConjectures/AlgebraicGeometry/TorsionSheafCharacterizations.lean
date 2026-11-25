/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.GroupTheory.Torsion
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90Etale
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.AlgebraicGeometry.GeometricStalkColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Characterizations of torsion abelian étale sheaves

Source: blueprint `sec-proper-base-change/sk-def-pbc`, statement, and
`sec-abelian-varieties/def-weil-pbc-etale-sheaves`
(blueprint: definition-torsion-sheaves--3).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: blueprint `sec-proper-base-change/sk-def-pbc`, statement
(blueprint: definition-torsion-sheaves--3).

Proof: (1) Exactness of geometric stalks (definition-torsion-sheaves--3) identifies
stalks of the kernel of multiplication by n with n-torsion in the stalk. Commutation with
colimits (definition-torsion-sheaves--3) identifies the stalk of the canonical colimit map
with inclusion of the union of these subgroups, namely the torsion subgroup.
(2) Conservativity (lemma-weil-pbc-geometric-stalk-conservative, Stacks 03PU) gives the first
condition iff every stalk is torsion. (3) Locally annihilated sections give torsion stalks:
represent a germ on a pointed neighbourhood and lift its geometric point to the covering
(definition-torsion-sheaves--3, Stacks 03PR).
(4) Conversely, choose a geometric point over each point of U; its germ is annihilated by a
positive integer. Equality with zero in the filtered stalk is witnessed on a smaller pointed
neighbourhood. These neighbourhoods cover U. The cofiltered-neighbourhood and composition
facts are definition-torsion-sheaves--3 and
definition-torsion-sheaves--3. Condition (2) is the recorded local-section
predicate `CategoryTheory.Sheaf.IsTorsion` (a covering sieve on whose arrows the restriction
has finite additive order), condition (3) is `IsAddTorsion` of every geometric stalk. -/
theorem isTorsionAbelianSheaf_characterizations {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (IsTorsionAbelianSheaf F ↔ F.IsTorsion) ∧
    (IsTorsionAbelianSheaf F ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
        IsAddTorsion (((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F)) := by
  classical
  have hstalk (hF : IsTorsionAbelianSheaf F) (Ω : Type u) [Field Ω]
      [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
      IsAddTorsion (((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F) := by
    have : Nonempty PNat.DvdOrder := ⟨⟨1, Nat.one_pos⟩⟩
    have : IsDirectedOrder PNat.DvdOrder := ⟨fun n m ↦
      ⟨⟨n.val * m.val, Nat.mul_pos n.val_pos m.val_pos⟩,
        dvd_mul_right n.val m.val, dvd_mul_left m.val n.val⟩⟩
    have : IsFiltered PNat.DvdOrder := inferInstance
    let D : PNat.DvdOrder ⥤ Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
      { obj := fun n ↦ kernel (n.val • 𝟙 F)
        map := fun {n m} hnm ↦ kernel.lift (m.val • 𝟙 F)
          (kernel.ι (n.val • 𝟙 F))
          (torsionKernelTransition_condition F n m hnm.down.down)
        map_id := fun n ↦ torsionKernelTransition_id F n
        map_comp := fun hnm hmk ↦
          (torsionKernelTransition_comp F _ _ _ hnm.down.down hmk.down.down).symm }
    let c : Cocone D :=
      { pt := F
        ι := { app := fun n ↦ kernel.ι (n.val • 𝟙 F)
               naturality := by intro n m hnm; simp [D] } }
    change IsIso (colimit.desc D c) at hF
    have := hF
    have : IsIso ((colimit.isColimit D).desc c) := hF
    have hc : IsColimit c := IsColimit.ofPointIso (colimit.isColimit D)
    let L := (pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})
    have : L.Additive := (pointSmallEtale t).sheafFiber_additive
    have hLc := isColimitOfPreserves L hc
    have := preservesFilteredColimitsOfSize_shrink.{0, u + 1, 0, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{u + 1})
    intro x
    obtain ⟨n, y, rfl⟩ := Concrete.isColimit_exists_rep (D ⋙ L) hLc x
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n.val, n.val_pos, ?_⟩
    have hk : L.map (kernel.ι (n.val • 𝟙 F)) ≫ L.map (n.val • 𝟙 F) = 0 := by
      rw [← Functor.map_comp, kernel.condition, Functor.map_zero]
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id] at hk
    have he := ConcreteCategory.congr_hom hk y
    simpa [L, c, ConcreteCategory.comp_apply] using he
  have hlocal : F.IsTorsion ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
        IsAddTorsion (((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F) := by
    refine ⟨fun hF Ω _ _ t ↦ ?_, fun h ↦ ?_⟩
    · exact (isTorsion_iff_isAddTorsion_sheafFiber F).mp hF Ω t
    · refine Sheaf.IsTorsion.of_isAddTorsion_sheafFiber
        (isConservativeFamilyOfPoints_ulift_pointSmallEtale T) ?_
      rintro ⟨-, ⟨x⟩⟩
      exact IsAddTorsion.of_surjective
        (f := ((((pointSmallEtale (T.algClosurePoint x)).uliftSheafFiberIso
          AddCommGrpCat.{u + 1}).app F).inv).hom)
        (ConcreteCategory.bijective_of_isIso _).2 (h _ _)
  have hiff : IsTorsionAbelianSheaf F ↔ F.IsTorsion := by
    refine ⟨fun hF ↦ hlocal.mpr (hstalk hF), fun hF ↦ ?_⟩
    classical
    have : Nonempty PNat.DvdOrder := ⟨⟨1, Nat.one_pos⟩⟩
    have : IsDirectedOrder PNat.DvdOrder := ⟨fun n m ↦
      ⟨⟨n.val * m.val, Nat.mul_pos n.val_pos m.val_pos⟩,
        dvd_mul_right n.val m.val, dvd_mul_left m.val n.val⟩⟩
    have : IsFiltered PNat.DvdOrder := inferInstance
    dsimp only [IsTorsionAbelianSheaf]
    let D : PNat.DvdOrder ⥤ Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
      { obj := fun n ↦ CategoryTheory.Limits.kernel (n.val • 𝟙 F)
        map := fun {n m} hnm ↦ CategoryTheory.Limits.kernel.lift (m.val • 𝟙 F)
          (CategoryTheory.Limits.kernel.ι (n.val • 𝟙 F))
          (torsionKernelTransition_condition F n m hnm.down.down)
        map_id := fun n ↦ torsionKernelTransition_id F n
        map_comp := fun hnm hmk ↦
          (torsionKernelTransition_comp F _ _ _ hnm.down.down hmk.down.down).symm }
    let c : CategoryTheory.Limits.Cocone D :=
      { pt := F
        ι := { app := fun n ↦ CategoryTheory.Limits.kernel.ι (n.val • 𝟙 F)
               naturality := by intro n m hnm; simp [D] } }
    change IsIso (CategoryTheory.Limits.colimit.desc D c)
    have : AB5OfSize.{0, 0} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
      AB5OfSize_shrink.{0, 0, u + 1, u + 1} _
    have : IsConnected PNat.DvdOrder := IsFiltered.isConnected _
    let φ := CategoryTheory.Limits.colimit.desc D c
    have hmono : Mono φ := by
      let α : D ⟶ (Functor.const _).obj F := { app n := c.ι.app n }
      have : ∀ n, Mono (α.app n) := fun n ↦
        inferInstanceAs (Mono (CategoryTheory.Limits.kernel.ι _))
      have : Mono α := NatTrans.mono_of_mono_app _
      have : Mono (CategoryTheory.Limits.colim.map α) := inferInstance
      let e := CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso
        (CategoryTheory.Limits.colimit.isColimit ((Functor.const PNat.DvdOrder).obj F))
        (CategoryTheory.Limits.isColimitConstCocone PNat.DvdOrder F)
      have : φ = CategoryTheory.Limits.colim.map α ≫ e.hom := by
        refine CategoryTheory.Limits.colimit.hom_ext fun n ↦ ?_
        simp [φ, e, α]
      rw [this]
      infer_instance
    have hepi : Epi φ := by
      have : Sheaf.IsLocallySurjective φ := by
        refine ⟨fun {V} s ↦ ?_⟩
        obtain ⟨R, hR, hRs⟩ := hF (U := Opposite.op V) s
        refine T.smallEtaleTopology.superset_covering ?_ hR
        intro W g hg
        obtain ⟨n, hn, hns⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (hRs hg)
        have hx : (n • 𝟙 F).hom.app (op W) (F.obj.map g.op s) = 0 := by
          change (((sheafToPresheaf _ _).map (n • 𝟙 F)).app (op W)) _ = 0
          rw [Functor.map_nsmul, NatTrans.app_nsmul]
          exact hns
        let E := sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
          (CategoryTheory.evaluation _ _).obj (op W)
        let e := PreservesKernel.iso E (n • 𝟙 F) ≪≫
          AddCommGrpCat.kernelIsoKer (E.map (n • 𝟙 F))
        let t := e.inv ⟨F.obj.map g.op s, hx⟩
        have ht : (kernel.ι (n • 𝟙 F)).hom.app (op W) t = F.obj.map g.op s := by
          change (e.inv ≫ E.map (kernel.ι (n • 𝟙 F))) ⟨F.obj.map g.op s, hx⟩ = _
          rw [Iso.trans_inv, Category.assoc, PreservesKernel.iso_inv_ι,
            AddCommGrpCat.kernelIsoKer_inv_comp_ι]
          rfl
        refine ⟨(CategoryTheory.Limits.colimit.ι D ⟨n, hn⟩).hom.app (Opposite.op W) t, ?_⟩
        rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
          ← ObjectProperty.FullSubcategory.comp_hom, CategoryTheory.Limits.colimit.ι_desc]
        exact ht
      exact Sheaf.epi_of_isLocallySurjective _
    exact isIso_of_mono_of_epi φ
  exact ⟨hiff, hiff.trans hlocal⟩

private theorem ratModInt_isAddTorsion :
    IsAddTorsion (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)) := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H q =>
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨q.den, q.pos, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    refine AddSubgroup.mem_zmultiples_iff.2 ⟨q.num, ?_⟩
    simp [nsmul_eq_mul, zsmul_eq_mul]

private theorem ratModInt_dyadic_not_killed (k : ℕ) (hk : 0 < k) :
    ∃ n : ℕ+, k • ((1 / (2 : ℚ) ^ (n : ℕ) : ℚ) :
      ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)) ≠ 0 := by
  let n : ℕ+ := ⟨k + 1, Nat.succ_pos _⟩
  refine ⟨n, fun h ↦ ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at h
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.1 h
  have hpow : k < 2 ^ (n : ℕ) := by
    exact lt_trans (Nat.lt_succ_self k) (Nat.lt_two_pow_self (n := k + 1))
  have hpos : (0 : ℚ) < (k : ℚ) / 2 ^ (n : ℕ) := by positivity
  have hlt : (k : ℚ) / 2 ^ (n : ℕ) < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast hpow
  have he : (z : ℚ) = (k : ℚ) / 2 ^ (n : ℕ) := by
    simpa [nsmul_eq_mul, zsmul_eq_mul, div_eq_mul_inv] using hz
  have hzpos : (0 : ℤ) < z := by exact_mod_cast (he ▸ hpos)
  have hzlt : z < (1 : ℤ) := by exact_mod_cast (he ▸ hlt)
  omega

-- The inherited statement names a nondependent index binder `n`.

-- The inherited statement names a nondependent index binder `n`.
set_option linter.unusedVariables false in
/-- Source: blueprint `sec-abelian-varieties/def-weil-pbc-etale-sheaves`, Q/Z example
(blueprint: definition-torsion-sheaves--3).

Proof: (5) The constant sheaf has geometric stalk Q/Z by
definition-torsion-sheaves--3, hence is torsion by the characterization above.
(6) The coproduct of positive-integer-indexed copies of T is étale over T, with disjoint open
coprojections (definition-torsion-sheaves--3). The sheaf condition gives the canonical
restriction isomorphism onto the product of sections on T: off-diagonal overlaps are empty,
and sections on the empty scheme form the zero group.
(7) For nonempty T, a geometric stalk identifies the composite of the constant-presheaf unit
and the germ map with the identity of Q/Z. Thus the unit is injective. The glued section with
coordinates 1/2^n cannot be killed by any k > 0, since 2^n > k for some n, and k/2^n is then
not an integer. The universe lift only places Q/Z in the sheaf's value universe. -/
theorem constant_ratModIntSheaf_sections_not_torsion (T : Scheme.{u}) :
    IsTorsionAbelianSheaf ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ))))) ∧
      (Nonempty T →
        ∃ (U : T.Etale) (e : U.left ≅ ∐ (fun _ : ℕ+ ↦ T))
          (j : ∀ n : ℕ+, Scheme.Etale.mk (𝟙 T) ⟶ U),
          U.hom = e.hom ≫ Sigma.desc (fun _ : ℕ+ ↦ 𝟙 T) ∧
          (∀ n : ℕ+, (j n).left = Sigma.ι (fun _ : ℕ+ ↦ T) n ≫ e.inv) ∧
          Function.Bijective (fun s : ((constantSheaf T.smallEtaleTopology
              AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of
                (ULift.{u + 1} (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ))))).obj.obj (op U) ↦
            fun n : ℕ+ ↦ ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
              (AddCommGrpCat.of (ULift.{u + 1} (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ))))).obj.map
                (j n).op s) ∧
          ∃ x : ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
              (AddCommGrpCat.of (ULift.{u + 1} (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ))))).obj.obj
                (op U),
            (∀ n : ℕ+, ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
                (AddCommGrpCat.of (ULift.{u + 1} (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ))))).obj.map
                  (j n).op x =
              (toSheafify T.smallEtaleTopology
                ((Functor.const T.Etaleᵒᵖ).obj
                  (AddCommGrpCat.of
                    (ULift.{u + 1} (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)))))).app
                      (op (Scheme.Etale.mk (𝟙 T)))
                        (ULift.up ((1 / (2 : ℚ) ^ (n : ℕ) : ℚ) :
                          ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)))) ∧
            ∀ k : ℕ, 0 < k → k • x ≠ 0) := by
  classical
  let E := AddCommGrpCat.of (ULift.{u + 1} (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)))
  let F := (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E
  have := preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
    (CategoryTheory.forget AddCommGrpCat.{u + 1})
  have hE : IsAddTorsion E := by
    intro x
    obtain ⟨n, hn, hnx⟩ :=
      isOfFinAddOrder_iff_nsmul_eq_zero.1 (ratModInt_isAddTorsion x.down)
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
    apply ULift.ext
    exact hnx
  refine ⟨(isTorsionAbelianSheaf_characterizations F).2.mpr ?_, ?_⟩
  · intro Ω _ _ t
    let g := (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj E)).app
      (op (Etale.mk (𝟙 T))) ≫
        (pointSmallEtale t).toPresheafFiber (Etale.mk (𝟙 T))
          (Over.homMk t (Category.comp_id t)) F.obj
    have : IsIso g := by
      let Φ := pointSmallEtale t
      have he : g = (Φ.sheafFiberConstantSheafIso E).inv := by
        let P := (Functor.const T.Etaleᵒᵖ).obj E
        have hι : Φ.toPresheafFiber (Etale.mk (𝟙 T))
            (Over.homMk t (Category.comp_id t)) P = (Φ.presheafFiberConstIso E).inv := by
          apply (cancel_mono (Φ.presheafFiberConstIso E).hom).1
          simp [P]
        exact (Φ.toPresheafFiber_naturality (toSheafify T.smallEtaleTopology P)
          (Etale.mk (𝟙 T)) (Over.homMk t (Category.comp_id t))).symm.trans
            (congrArg (fun f ↦ f ≫ Φ.presheafFiber.map (toSheafify T.smallEtaleTopology P)) hι)
      rw [he]
      infer_instance
    exact IsAddTorsion.of_surjective (f := g.hom)
      (ConcreteCategory.bijective_of_isIso g).2 hE
  · intro hT
    let f : (∐ (fun _ : ℕ+ ↦ T)) ⟶ T := Sigma.desc (fun _ : ℕ+ ↦ 𝟙 T)
    have hf : AlgebraicGeometry.Etale f :=
      IsZariskiLocalAtSource.sigmaDesc (P := @AlgebraicGeometry.Etale) (fun _ ↦ inferInstance)
    let U : T.Etale := Etale.mk f
    let j (n : ℕ+) : Etale.mk (𝟙 T) ⟶ U :=
      MorphismProperty.Over.homMk (A := Etale.mk (𝟙 T)) (B := U)
        (Sigma.ι (fun _ : ℕ+ ↦ T) n) (by
        change Sigma.ι (fun _ : ℕ+ ↦ T) n ≫ f = 𝟙 T
        exact Sigma.ι_comp_desc _ _)
    have hcov : ⋃ n, Set.range (j n).left = Set.univ := by
      exact (sigmaOpenCover (fun _ : ℕ+ ↦ T)).iUnion_range
    have hbij : Function.Bijective
        (fun s : F.obj.obj (op U) ↦ fun n : ℕ+ ↦ F.obj.map (j n).op s) := by
      constructor
      · intro a b hab
        exact (isSheafFor_ofArrows F j hcov).isSeparatedFor.ext
          (fun Z g ⟨n⟩ ↦ congrFun hab n)
      · intro a
        obtain ⟨x, hx, -⟩ := (Presieve.isSheafFor_arrows_iff _ j).1
          (isSheafFor_ofArrows F j hcov) a (fun i l Z gi gl h ↦ by
            by_cases hil : i = l
            · subst l
              have he : gi = gl := MorphismProperty.Over.Hom.ext
                ((cancel_mono (Sigma.ι (fun _ : ℕ+ ↦ T) i)).1
                  (congrArg (fun φ ↦ φ.left) h))
              subst gl
              rfl
            · have : IsEmpty Z.left := isEmpty_of_commSq_sigmaι_of_ne
                ⟨congrArg (fun φ ↦ φ.left) h⟩ hil
              exact (subsingleton_obj_of_isEmpty F).elim _ _)
        exact ⟨x, funext hx⟩
    refine ⟨U, Iso.refl _, j, ?_, ?_, hbij, ?_⟩
    · simp [U, f]
    · intro n
      change Sigma.ι (fun _ : ℕ+ ↦ T) n = Sigma.ι (fun _ : ℕ+ ↦ T) n ≫ 𝟙 _
      exact (Category.comp_id _).symm
    · let c := (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj E)).app
        (op (Etale.mk (𝟙 T)))
      let a (n : ℕ+) : E := ULift.up
        ((1 / (2 : ℚ) ^ (n : ℕ) : ℚ) : ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ))
      obtain ⟨x, hx⟩ := hbij.2 (fun n ↦ c (a n))
      refine ⟨x, fun n ↦ congrFun hx n, ?_⟩
      let t := T.algClosurePoint (Classical.choice hT)
      let g := (pointSmallEtale t).toPresheafFiber (Etale.mk (𝟙 T))
        (Over.homMk t (Category.comp_id t)) F.obj
      have : IsIso (c ≫ g) := by
        let Φ := pointSmallEtale t
        have he : c ≫ g = (Φ.sheafFiberConstantSheafIso E).inv := by
          let P := (Functor.const T.Etaleᵒᵖ).obj E
          have hι : Φ.toPresheafFiber (Etale.mk (𝟙 T))
              (Over.homMk t (Category.comp_id t)) P = (Φ.presheafFiberConstIso E).inv := by
            apply (cancel_mono (Φ.presheafFiberConstIso E).hom).1
            simp [P]
          exact (Φ.toPresheafFiber_naturality (toSheafify T.smallEtaleTopology P)
            (Etale.mk (𝟙 T)) (Over.homMk t (Category.comp_id t))).symm.trans
              (congrArg (fun f ↦ f ≫ Φ.presheafFiber.map (toSheafify T.smallEtaleTopology P)) hι)
        rw [he]
        infer_instance
      have hc : Function.Injective c := by
        intro a b hab
        exact (ConcreteCategory.bijective_of_isIso (c ≫ g)).1
          (by
            change g.hom (c.hom a) = g.hom (c.hom b)
            exact congrArg g.hom hab)
      intro k hk hzero
      obtain ⟨n, hn⟩ := ratModInt_dyadic_not_killed k hk
      have hnzero : k • a n = (0 : E) := hc (by
        have he := congrArg (F.obj.map (j n).op) hzero
        have hxn : F.obj.map (j n).op x = c (a n) := congrFun hx n
        rw [map_nsmul, map_zero, hxn] at he
        simpa only [map_nsmul, map_zero] using he)
      exact hn (congrArg ULift.down hnzero)




end AlgebraicGeometry.Scheme
