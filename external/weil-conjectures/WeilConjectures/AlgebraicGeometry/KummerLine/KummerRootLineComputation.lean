/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KummerLine.KummerLineGeometry
public import Mathlib.Algebra.Module.ZMod

import WeilConjectures.AlgebraicGeometry.AffinePuncturedLine.AffinePuncturedLineAlgebra
import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Prod
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Roots-of-unity computation on the two lines

## References

* Stacks, Tag 03PK
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Roots-of-unity cohomology is killed by `m`, hence has its unique `ZMod m` action. -/
theorem kummerRootCohomology_annihilated (X : Scheme.{u}) (m q : ℕ)
    (x : Sheaf.H (X.rootsOfUnitySheaf m) q) : m • x = 0 := by
  have h : m • 𝟙 (X.rootsOfUnitySheaf m) = 0 := by
    change m • 𝟙 (kernel (m • 𝟙 X.gmSheaf)) = 0
    rw [← cancel_mono (kernel.ι (m • 𝟙 X.gmSheaf)), Preadditive.nsmul_comp,
      Category.id_comp, zero_comp, ← Category.comp_id (kernel.ι _),
      ← Preadditive.comp_nsmul, kernel.condition]
  have hx := congrArg (fun f ↦ Sheaf.H.map f q x) h
  rw [Sheaf.H.map_nsmul_apply, Sheaf.H.map_id_apply, Sheaf.H.map_apply,
    Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero] at hx
  exact hx

/-- The unique residue-ring action on roots-of-unity cohomology. -/
instance kummerRootCohomologyModule (X : Scheme.{u}) (m q : ℕ) :
    Module (ULift.{u + 1} (ZMod m)) (Sheaf.H (X.rootsOfUnitySheaf m) q) :=
  letI := AddCommGroup.zmodModule (kummerRootCohomology_annihilated X m q)
  Module.compHom _ ULift.ringEquiv.toRingHom

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.KummerLine

attribute [local irreducible] Scheme.kummerδ₀

private def residueLinearMap (m : ℕ) {M P : Type (u + 1)}
    [AddCommGroup M] [AddCommGroup P]
    [Module (ULift.{u + 1} (ZMod m)) M] [Module (ULift.{u + 1} (ZMod m)) P]
    (f : M →+ P) : M →ₗ[ULift.{u + 1} (ZMod m)] P :=
  { f with
    map_smul' := by
      intro r x
      have hr : r = ((ZMod.cast r.down : ℤ) : ULift.{u + 1} (ZMod m)) := by
        apply ULift.ext
        exact (ZMod.intCast_zmod_cast r.down).symm
      change f (r • x) = r • f x
      rw [hr, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul] }

private def residueLinearEquiv (m : ℕ) {M P : Type (u + 1)}
    [AddCommGroup M] [AddCommGroup P]
    [Module (ULift.{u + 1} (ZMod m)) M] [Module (ULift.{u + 1} (ZMod m)) P]
    (e : M ≃+ P) : M ≃ₗ[ULift.{u + 1} (ZMod m)] P :=
  { e with map_smul' := (residueLinearMap m e.toAddMonoidHom).map_smul }

private lemma zero_trivialization (X : Scheme.{u}) [ConnectedSpace X]
    (m : ℕ) [NeZero m] (a : Γ(X, ⊤)ˣ) (ha : a ^ m = 1)
    [IsIso (X.constantZModToRootsOfUnitySheaf m a ha)] :
    ∃ e : ULift.{u + 1} (ZMod m) ≃ₗ[ULift.{u + 1} (ZMod m)]
        Sheaf.H (X.rootsOfUnitySheaf m) 0,
      (kernel.ι (m • 𝟙 X.gmSheaf)).hom.app (op (Scheme.Etale.mk (𝟙 X)))
        (Sheaf.H.equiv₀ (X.rootsOfUnitySheaf m)
          (MorphismProperty.Over.mkIdTerminal @Etale X) (e 1)) =
          ULift.up (Additive.ofMul a) := by
  let θ := X.constantZModToRootsOfUnitySheaf m a ha
  let T := Scheme.Etale.mk (𝟙 X)
  let hT := MorphismProperty.Over.mkIdTerminal @Etale X
  let c : ULift.{u + 1} (ZMod m) ≃+ (X.constantZMod m).obj.obj (op T) :=
    AddEquiv.ofBijective
    ((toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod m))))).app
        (op T)).hom (X.bijective_toSheafify_app_terminal _)
  let d := (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⋙
    (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op T)).mapIso (asIso θ))
  let e : ULift.{u + 1} (ZMod m) ≃+ Sheaf.H (X.rootsOfUnitySheaf m) 0 :=
    c.trans (d.addCommGroupIsoToAddEquiv.trans (Sheaf.H.equiv₀ (X.rootsOfUnitySheaf m) hT).symm)
  refine ⟨residueLinearEquiv m e, ?_⟩
  change (kernel.ι (m • 𝟙 X.gmSheaf)).hom.app (op T)
    ((Sheaf.H.equiv₀ (X.rootsOfUnitySheaf m) hT) (e 1)) = ULift.up (Additive.ofMul a)
  change (kernel.ι (m • 𝟙 X.gmSheaf)).hom.app (op T)
    ((Sheaf.H.equiv₀ (X.rootsOfUnitySheaf m) hT)
      ((Sheaf.H.equiv₀ (X.rootsOfUnitySheaf m) hT).symm
        (d.addCommGroupIsoToAddEquiv (c 1)))) = _
  have heq := (Sheaf.H.equiv₀ (X.rootsOfUnitySheaf m) hT).apply_symm_apply
    (d.addCommGroupIsoToAddEquiv (c 1))
  refine (congrArg ((kernel.ι (m • 𝟙 X.gmSheaf)).hom.app (op T)) heq).trans ?_
  change (kernel.ι (m • 𝟙 X.gmSheaf)).hom.app (op T)
    (θ.hom.app (op T) (c 1)) = ULift.up (Additive.ofMul a)
  have hfac : toSheafify X.smallEtaleTopology _ ≫ θ.hom ≫
      (kernel.ι (m • 𝟙 X.gmSheaf)).hom = X.zmodToGmPresheaf m a ha := by
    have hh : θ.hom ≫ (kernel.ι (m • 𝟙 X.gmSheaf)).hom =
        (X.constantZModToGmSheaf m a ha).hom :=
      congrArg (fun φ : X.constantZMod m ⟶ X.gmSheaf ↦ φ.hom)
        (kernel.lift_ι (m • 𝟙 X.gmSheaf) (X.constantZModToGmSheaf m a ha)
          (X.constantZModToGmSheaf_comp_nsmul m a ha))
    rw [hh]
    exact X.toSheafify_constantZModToGmSheaf m a ha
  have hh := congrArg (fun f ↦ (f.app (op T)) (1 : ULift.{u + 1} (ZMod m))) hfac
  change _ = (X.zmodToGmPresheaf m a ha).app (op T) (ULift.up (1 : ZMod m)) at hh
  change (kernel.ι (m • 𝟙 X.gmSheaf)).hom.app (op T)
    (θ.hom.app (op T) (c 1)) = _ at hh
  refine hh.trans ?_
  apply ULift.ext
  apply Additive.toMul.injective
  apply Units.ext
  have h := X.zmodToGmPresheaf_app_natCast m a ha (op T) 1
  simp only [Nat.cast_one, pow_one] at h
  exact h.trans (by rfl)

private lemma root_zero (k : Type u) [Field k] (m : ℕ) [NeZero m]
    (ζ : kˣ) (hζ : IsPrimitiveRoot ζ m) (b : Bool) :
    ∃ e : ULift.{u + 1} (ZMod m) ≃ₗ[ULift.{u + 1} (ZMod m)]
        Sheaf.H ((curve k b).rootsOfUnitySheaf m) 0,
      (kernel.ι (m • 𝟙 (curve k b).gmSheaf)).hom.app
        (op (Scheme.Etale.mk (𝟙 (curve k b))))
        (Sheaf.H.equiv₀ ((curve k b).rootsOfUnitySheaf m)
              (MorphismProperty.Over.mkIdTerminal @Etale (curve k b)) (e 1)) =
          ULift.up (Additive.ofMul (Units.map (scalar k b).toMonoidHom ζ)) := by
  let X := curve k b
  have : ConnectedSpace X := by
    cases b
    · change ConnectedSpace (PrimeSpectrum (Polynomial k))
      infer_instance
    · change ConnectedSpace (PrimeSpectrum (LaurentPolynomial k))
      infer_instance
  let a := Units.map (scalar k b).toMonoidHom ζ
  have ha : a ^ m = 1 := by
    change (Units.map (scalar k b).toMonoidHom ζ) ^ m = 1
    rw [← map_pow, hζ.pow_eq_one, map_one]
  let θ := X.constantZModToRootsOfUnitySheaf m a ha
  have : IsIso θ := X.isIso_constantZModToRootsOfUnitySheaf m (structureMap k b)
    (IsPrimitiveRoot.coe_units_iff.mpr hζ) a ha rfl
  exact zero_trivialization X m a ha

private lemma line_curve (k : Type u) [Field k] (b : Bool) :
    IsCurve (structureMap k b) := by
  have hdim : topologicalKrullDim (curve k false) ≤ 1 := by
    change topologicalKrullDim (PrimeSpectrum (Polynomial k)) ≤ 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    rfl
  have hopen : IsOpenImmersion (inclusion k) :=
    IsOpenImmersion.of_isLocalization (S := LaurentPolynomial k) Polynomial.X
  have hcomp : inclusion k ≫ structureMap k false = structureMap k true := by
    rw [inclusion, structureMap, structureMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro x
    exact Polynomial.toLaurent_C x
  have hfinite : LocallyOfFiniteType (structureMap k false) := by
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom Polynomial.C))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  have hsep (b : Bool) : IsSeparated (structureMap k b) := by
    cases b <;> dsimp [structureMap, curve] <;> infer_instance
  have hqc (b : Bool) : QuasiCompact (structureMap k b) := by
    cases b <;> dsimp [structureMap, curve] <;> infer_instance
  have hfalse : IsCurve (structureMap k false) := { krullDim_le_one := hdim }
  cases b
  · exact hfalse
  · have : LocallyOfFiniteType (structureMap k true) := by
      rw [← hcomp]
      infer_instance
    exact { krullDim_le_one :=
      (inclusion k).isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hdim }

private lemma root_higher (k : Type u) [Field k] [IsAlgClosed k]
    (m : ℕ) [NeZero m] (ζ : kˣ) (_hζ : IsPrimitiveRoot ζ m)
    (b : Bool) (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H ((curve k b).rootsOfUnitySheaf m) q) := by
  have : IsCurve (structureMap k b) := line_curve k b
  have : IsAffine (curve k b) := by cases b <;> dsimp [curve] <;> infer_instance
  have ht : ((curve k b).rootsOfUnitySheaf m).IsTorsion := by
    refine Scheme.isTorsion_of_nsmul_id_eq_zero
      (Nat.pos_of_ne_zero (NeZero.ne m))
      ((cancel_mono (kernel.ι (m • 𝟙 (curve k b).gmSheaf))).1 ?_)
    rw [Preadditive.nsmul_comp, Category.id_comp, zero_comp,
      ← Category.comp_id (kernel.ι (m • 𝟙 (curve k b).gmSheaf)),
      ← Preadditive.comp_nsmul, kernel.condition]
  exact IsCurve.subsingleton_sheafH_of_two_le_of_isAffine (structureMap k b) _ ht q hq

private lemma terminal_naturality (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {T S : X.Etale} (hT : IsTerminal T) (hS : IsTerminal S) (x : Sheaf.H F 0) :
    F.obj.map (hT.from S).op (Sheaf.H.equiv₀ F hT x) = Sheaf.H.equiv₀ F hS x := by
  exact (Sheaf.H.equiv₀_congr hT hS F x).symm

private lemma root_restriction_sections (X Y : Scheme.{u}) (f : Y ⟶ X) (m : ℕ)
    (a : Γ(X, ⊤)ˣ) (c : Γ(Y, ⊤)ˣ)
    (hac : Units.map f.appTop.hom.toMonoidHom a = c)
    (x : Sheaf.H (X.rootsOfUnitySheaf m) 0)
    (y : Sheaf.H (Y.rootsOfUnitySheaf m) 0)
    (hx : (kernel.ι (m • 𝟙 X.gmSheaf)).hom.app (op (Scheme.Etale.mk (𝟙 X)))
      (Sheaf.H.equiv₀ (X.rootsOfUnitySheaf m)
        (MorphismProperty.Over.mkIdTerminal @Etale X) x) = ULift.up (Additive.ofMul a))
    (hy : (kernel.ι (m • 𝟙 Y.gmSheaf)).hom.app (op (Scheme.Etale.mk (𝟙 Y)))
      (Sheaf.H.equiv₀ (Y.rootsOfUnitySheaf m)
        (MorphismProperty.Over.mkIdTerminal @Etale Y) y) = ULift.up (Additive.ofMul c)) :
    Scheme.rootsOfUnityCohomologyMap f m 0 x = y := by
  have hsection (Z : Scheme.{u}) (a : Γ(Z, ⊤)ˣ)
      (z : Sheaf.H (Z.rootsOfUnitySheaf m) 0)
      (hz : (kernel.ι (m • 𝟙 Z.gmSheaf)).hom.app (op (Scheme.Etale.mk (𝟙 Z)))
        (Sheaf.H.equiv₀ (Z.rootsOfUnitySheaf m)
          (MorphismProperty.Over.mkIdTerminal @Etale Z) z) = ULift.up (Additive.ofMul a)) :
      Sheaf.H.equiv₀ Z.gmSheaf terminalIsTerminal
        (Sheaf.H.map (Z.rootsOfUnitySheafι m) 0 z) = Scheme.gmSection a := by
    let hT := MorphismProperty.Over.mkIdTerminal @Etale Z
    rw [← terminal_naturality Z Z.gmSheaf hT terminalIsTerminal,
      ← Sheaf.H.equiv₀_naturality]
    exact (congrArg (Z.gmSheaf.obj.map ((hT).from (⊤_ Z.Etale)).op) hz).trans (by rfl)
  have hinj : Function.Injective (Sheaf.H.map (Y.rootsOfUnitySheafι m) 0) := by
    intro v w heq
    let hT := MorphismProperty.Over.mkIdTerminal @Etale Y
    apply (Sheaf.H.equiv₀ (Y.rootsOfUnitySheaf m) hT).injective
    apply Y.injective_kernelι_app m _
    exact (Sheaf.H.equiv₀_naturality (hT := hT) (Y.rootsOfUnitySheafι m) v).trans
      ((congrArg (Sheaf.H.equiv₀ Y.gmSheaf hT) heq).trans
        (Sheaf.H.equiv₀_naturality (hT := hT) (Y.rootsOfUnitySheafι m) w).symm)
  apply hinj
  apply (Sheaf.H.equiv₀ Y.gmSheaf terminalIsTerminal).injective
  rw [Scheme.map_kernelι_rootsOfUnityCohomologyMap,
    Scheme.equiv₀_gmCohomologyMap_zero, hsection X a x hx, hsection Y c y hy,
    Scheme.gmSectionsPullback_gmSection, hac]

private lemma root_restriction_zero (k : Type u) [Field k] (m : ℕ) (ζ : kˣ)
    (z : (b : Bool) → Sheaf.H ((curve k b).rootsOfUnitySheaf m) 0)
    (hz : ∀ b : Bool,
      (kernel.ι (m • 𝟙 (curve k b).gmSheaf)).hom.app
        (op (Scheme.Etale.mk (𝟙 (curve k b))))
        (Sheaf.H.equiv₀ ((curve k b).rootsOfUnitySheaf m)
              (MorphismProperty.Over.mkIdTerminal @Etale (curve k b)) (z b)) =
      ULift.up (Additive.ofMul (Units.map (scalar k b).toMonoidHom ζ))) :
    rootRestriction k m 0 (z false) = z true := by
  apply root_restriction_sections (curve k false) (curve k true) (inclusion k) m
    (Units.map (scalar k false).toMonoidHom ζ)
    (Units.map (scalar k true).toMonoidHom ζ) ?_ (z false) (z true) (hz false) (hz true)
  apply Units.ext
  have hcomp : inclusion k ≫ structureMap k false = structureMap k true := by
    rw [inclusion, structureMap, structureMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro x
    exact Polynomial.toLaurent_C x
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (structureMap k false).appTop ≫
    (inclusion k).appTop) (ζ : k) = _
  rw [← Scheme.Hom.comp_appTop, hcomp]
  rfl

private lemma degree_one_boundary (k : Type u) [Field k] (b : Bool) (m : ℕ)
    (hm : IsUnit (m : Γ(curve k b, ⊤))) :
    Function.Surjective ((curve k b).kummerδ₀ m hm) := by
  have hp : Subsingleton (curve k b).Pic := by
    cases b
    · exact (AffinePuncturedLine.affine_punctured_line_algebra k).2.2.1
    · exact (AffinePuncturedLine.affine_punctured_line_algebra k).2.2.2.1
  let := hp
  have : Subsingleton (curve k b).CohomologicalPicardGroup :=
    (Scheme.Pic.toCohomologicalPicardGroupAddEquiv (curve k b)).symm.injective.subsingleton
  intro y
  exact ((curve k b).exact_sheafH_rootsOfUnitySheaf_one m hm).2.1 y |>.mp
    (Subsingleton.elim _ _)

private lemma boundary_subsingleton (X : Scheme.{u}) (m : ℕ)
    (hm : IsUnit (m : Γ(X, ⊤)))
    (hsurj : Function.Surjective (X.kummerδ₀ m hm))
    (hpow : ∀ a : Γ(X, ⊤)ˣ, ∃ c : Γ(X, ⊤)ˣ, c ^ m = a) :
    Subsingleton (Sheaf.H (X.rootsOfUnitySheaf m) 1) := by
  have hzero (x : Sheaf.H (X.rootsOfUnitySheaf m) 1) : x = 0 := by
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨c, hc⟩ := hpow a.toMul
    apply (AddMonoidHom.mem_ker).mp
    rw [(X.exact_sheafH_rootsOfUnitySheaf_one m hm).1]
    refine ⟨Additive.ofMul c, ?_⟩
    apply Additive.toMul.injective
    simpa only [zsmulAddGroupHom_apply, toMul_zsmul, toMul_ofMul, zpow_natCast] using hc
  exact ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩

private lemma root_affine_one (k : Type u) [Field k] [IsAlgClosed k]
    (m : ℕ) (hmpos : 1 ≤ m) (hmk : IsUnit (m : k)) :
    Subsingleton (Sheaf.H ((curve k false).rootsOfUnitySheaf m) 1) := by
  let X := curve k false
  have hm : IsUnit (m : Γ(X, ⊤)) := by simpa using hmk.map (scalar k false)
  have hdiv : ∀ a : kˣ, ∃ c : kˣ, c ^ m = a :=
    ((AffinePuncturedLine.affine_punctured_line_algebra k).2.2.2.2 m hmpos hmk).2.2
      inferInstance
  have hpow : ∀ a : Γ(X, ⊤)ˣ, ∃ c : Γ(X, ⊤)ˣ, c ^ m = a := by
    intro a
    obtain ⟨b, hb⟩ := (AffinePuncturedLine.affine_punctured_line_algebra k).1.2
      (Multiplicative.ofAdd (ULift.up (Additive.ofMul a)))
    obtain ⟨c, hc⟩ := hdiv b
    refine ⟨Units.map
      (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom.toMonoidHom
      (Units.map Polynomial.C.toMonoidHom c), ?_⟩
    have hb' := congrArg (fun t ↦ Additive.toMul (Multiplicative.toAdd t).down) hb
    change Units.map (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom.toMonoidHom
      (Units.map Polynomial.C.toMonoidHom b) = a at hb'
    rw [← hb', ← hc, map_pow, map_pow]
  exact boundary_subsingleton X m hm (degree_one_boundary k false m hm) hpow

private lemma quotient_generator {G H : Type (u + 1)} [CommGroup G] [CommGroup H]
    (m : ℕ) (μ : G →* H) (hsurj : Function.Surjective μ)
    (hker : (powMonoidHom m).range = μ.ker)
    (ev : (G ⧸ (powMonoidHom m).range) ≃* Multiplicative (ZMod m))
    (t : G) (ht : ev (QuotientGroup.mk t) = Multiplicative.ofAdd (1 : ZMod m)) :
    ∃ e : ZMod m ≃+ Additive H, e 1 = Additive.ofMul (μ t) := by
  let eδ := QuotientGroup.liftEquiv (powMonoidHom m).range hsurj hker
  let E := ev.symm.trans eδ
  let e : ZMod m ≃+ Additive H :=
    (AddEquiv.additiveMultiplicative (ZMod m)).symm.trans E.toAdditive
  refine ⟨e, ?_⟩
  change Additive.ofMul (eδ (ev.symm (Multiplicative.ofAdd (1 : ZMod m)))) = _
  rw [← ht, MulEquiv.symm_apply_apply]
  rfl

private lemma coordinate_section (k : Type u) [Field k] :
    Additive.toMul (AffinePuncturedLine.specUnitSection (LaurentPolynomial k)
      (AffinePuncturedLine.laurentUnit k 1 1)).toAdd.down = coordinateUnit k := by
  change Units.map _ (AffinePuncturedLine.laurentUnit k 1 1) = coordinateUnit k
  apply Units.ext
  change (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv
      (LaurentPolynomial.C (1 : k) * LaurentPolynomial.T (1 : ℤ)) = _
  simp only [map_one, one_mul]
  rfl

private lemma boundary_kernel (X : Scheme.{u}) (m : ℕ)
    (hm : IsUnit (m : Γ(X, ⊤))) :
    (powMonoidHom m).range =
      ((X.kummerδ₀ m hm).comp AddEquiv.ulift.toAddMonoidHom).toMultiplicative.ker := by
  let δ := X.kummerδ₀ m hm
  ext x
  change (∃ y, y ^ m = x) ↔ δ x.toAdd.down = 0
  rw [← AddMonoidHom.mem_ker, (X.exact_sheafH_rootsOfUnitySheaf_one m hm).1]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y.toAdd.down, ?_⟩
    change (m : ℤ) • y.toAdd.down = (y ^ m).toAdd.down
    rw [toAdd_pow, ULift.smul_down, natCast_zsmul]
  · rintro ⟨y, hy⟩
    refine ⟨Multiplicative.ofAdd (ULift.up y), ?_⟩
    apply Multiplicative.toAdd.injective
    apply ULift.ext
    change (m : ℤ) • y = x.toAdd.down at hy
    change m • y = x.toAdd.down
    simpa only [natCast_zsmul] using hy

-- Avoid unfolding the connecting map when comparing the normalized generator.
attribute [local irreducible] generator

private lemma boundary_equiv_of_quotient (X : Scheme.{u}) (m : ℕ)
    (hm : IsUnit (m : Γ(X, ⊤)))
    (hsurj : Function.Surjective (X.kummerδ₀ m hm))
    (ev : (Multiplicative (ULift.{u + 1} (Additive Γ(X, ⊤)ˣ)) ⧸
      (powMonoidHom m).range) ≃* Multiplicative (ZMod m))
    (t : Γ(X, ⊤)ˣ)
    (ht : ev (QuotientGroup.mk (Multiplicative.ofAdd (ULift.up (Additive.ofMul t)))) =
      Multiplicative.ofAdd (1 : ZMod m)) :
    ∃ e : ULift.{u + 1} (ZMod m) ≃ₗ[ULift.{u + 1} (ZMod m)]
        Sheaf.H (X.rootsOfUnitySheaf m) 1,
      e 1 = X.kummerδ₀ m hm (Additive.ofMul t) := by
  let H := Sheaf.H (X.rootsOfUnitySheaf m) 1
  let δ := X.kummerδ₀ m hm
  let μ := (δ.comp AddEquiv.ulift.toAddMonoidHom).toMultiplicative
  have hμ : Function.Surjective μ := by
    intro y
    obtain ⟨a, ha⟩ := hsurj y.toAdd
    exact ⟨Multiplicative.ofAdd (ULift.up a), congrArg Multiplicative.ofAdd ha⟩
  obtain ⟨ea, hea⟩ := quotient_generator m μ hμ (boundary_kernel X m hm) ev
    (Multiplicative.ofAdd (ULift.up (Additive.ofMul t))) ht
  let e : ULift.{u + 1} (ZMod m) ≃+ H :=
    AddEquiv.ulift.trans (ea.trans (AddEquiv.additiveMultiplicative H))
  refine ⟨residueLinearEquiv m e, ?_⟩
  change (AddEquiv.additiveMultiplicative H) (ea (1 : ZMod m)) = _
  rw [hea]
  rfl

private lemma root_one (k : Type u) [Field k] [IsAlgClosed k]
    (m : ℕ) (hmpos : 1 ≤ m) (hmk : IsUnit (m : k))
    (hm : IsUnit (m : Γ(curve k true, ⊤))) :
    ∃ e : ULift.{u + 1} (ZMod m) ≃ₗ[ULift.{u + 1} (ZMod m)]
        Sheaf.H ((curve k true).rootsOfUnitySheaf m) 1,
      e 1 = generator k m hm := by
  classical
  have hdiv := ((AffinePuncturedLine.affine_punctured_line_algebra k).2.2.2.2
    m hmpos hmk).2.2 inferInstance
  have hscalar : Subsingleton (kˣ ⧸ (powMonoidHom m).range) := by
    refine ⟨fun x y ↦ ?_⟩
    have hzero (x : kˣ ⧸ (powMonoidHom m).range) : x = 1 := by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      exact (QuotientGroup.eq_one_iff _).mpr (hdiv a)
    exact (hzero x).trans (hzero y).symm
  let := hscalar
  let : Unique (kˣ ⧸ (powMonoidHom m).range) := Unique.mk' _
  obtain ⟨eu, heu⟩ := ((AffinePuncturedLine.affine_punctured_line_algebra k).2.2.2.2
    m hmpos hmk).1
  let ev := eu.trans ((MulEquiv.uniqueProd :
    (kˣ ⧸ (powMonoidHom m).range) × Multiplicative (ZMod m) ≃*
      Multiplicative (ZMod m)))
  let t := AffinePuncturedLine.specUnitSection (LaurentPolynomial k)
    (AffinePuncturedLine.laurentUnit k 1 1)
  have ht : ev (QuotientGroup.mk t) = Multiplicative.ofAdd (1 : ZMod m) := by
    change (eu (QuotientGroup.mk t)).2 = _
    rw [heu]
    simp
  obtain ⟨e, he⟩ := boundary_equiv_of_quotient (curve k true) m hm
    (degree_one_boundary k true m hm) ev t.toAdd.down.toMul ht
  refine ⟨e, he.trans ?_⟩
  unfold generator
  apply congrArg ((curve k true).kummerδ₀ m hm)
  apply Additive.toMul.injective
  exact coordinate_section k


/-- Roots-of-unity cohomology on the affine and punctured lines, with the actual Kummer
boundary of the coordinate as the degree-one generator. -/
theorem kummer_root_line_computation (k : Type u) [Field k] [IsAlgClosed k]
    (m : ℕ) (hmpos : 1 ≤ m) (hmk : IsUnit (m : k))
    (ζ : kˣ) (hζ : IsPrimitiveRoot ζ m)
    (hm : IsUnit (m : Γ(curve k true, ⊤))) :
    ∃ z : (b : Bool) → Sheaf.H ((curve k b).rootsOfUnitySheaf m) 0,
      (∀ b : Bool,
        (kernel.ι (m • 𝟙 (curve k b).gmSheaf)).hom.app
            (op (Scheme.Etale.mk (𝟙 (curve k b))))
            (Sheaf.H.equiv₀ ((curve k b).rootsOfUnitySheaf m)
              (MorphismProperty.Over.mkIdTerminal @Etale (curve k b)) (z b)) =
          ULift.up (Additive.ofMul (Units.map (scalar k b).toMonoidHom ζ))) ∧
      rootRestriction k m 0 (z false) = z true ∧
      (∀ b : Bool, ∃ e : ULift.{u + 1} (ZMod m) ≃ₗ[ULift.{u + 1} (ZMod m)]
          Sheaf.H ((curve k b).rootsOfUnitySheaf m) 0, e 1 = z b) ∧
      (∀ (b : Bool) (q : ℕ), (if b then 1 else 0) < q →
        Subsingleton (Sheaf.H ((curve k b).rootsOfUnitySheaf m) q)) ∧
      (∃ e : ULift.{u + 1} (ZMod m) ≃ₗ[ULift.{u + 1} (ZMod m)]
          Sheaf.H ((curve k true).rootsOfUnitySheaf m) 1,
        e 1 = generator k m hm) := by
  classical
  let : NeZero m := ⟨by omega⟩
  choose e he using fun b ↦ root_zero k m ζ hζ b
  let z (b : Bool) := e b 1
  refine ⟨z, he, root_restriction_zero k m ζ z he, ?_, ?_, root_one k m hmpos hmk hm⟩
  · intro b
    exact ⟨e b, rfl⟩
  · intro b q hq
    cases b
    · by_cases hq1 : q = 1
      · subst q
        exact root_affine_one k m hmpos hmk
      · exact root_higher k m ζ hζ false q (by
          simp only [Bool.false_eq_true, ↓reduceIte] at hq
          omega)
    · exact root_higher k m ζ hζ true q (by simpa only [↓reduceIte] using hq)


end AlgebraicGeometry.KummerLine
