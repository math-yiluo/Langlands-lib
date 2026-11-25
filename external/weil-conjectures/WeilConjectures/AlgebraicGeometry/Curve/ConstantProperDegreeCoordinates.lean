/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
import WeilConjectures.AlgebraicGeometry.BaseChangeCurve
import WeilConjectures.AlgebraicGeometry.Curve.ConstantKummerNaturality
import WeilConjectures.AlgebraicGeometry.Curve.Kummer
import WeilConjectures.AlgebraicGeometry.Curve.Picard
import WeilConjectures.AlgebraicGeometry.Curve.PicProperNTorsionDiv
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism

/-!
# Degree-normalized proper cohomology coordinates

Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance,
proof of proposition-cohomology-smooth-affine-curve, proper case in degree two
(blueprint: lem-sc-constant-proper-degree-coordinates).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

private theorem proper_compactification_genus_aux
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g] :
    f.genus = c.g.genus := by
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have : IsProper c.g := c.isProper
  have : IsProper (c.i ≫ c.g) := c.comm ▸ inferInstance
  have : IsProper c.i := .of_comp c.i c.g
  have : ConnectedSpace C := IsConnectedCurve.connectedSpace (f := f)
  have : ConnectedSpace c.Z := IsConnectedCurve.connectedSpace (f := c.g)
  have hrange : Set.range c.i.base = Set.univ :=
    IsClopen.eq_univ ⟨c.i.isClosedMap.isClosed_range, c.i.isOpenEmbedding.isOpen_range⟩
      (Set.range_nonempty c.i.base)
  have : Surjective c.i := ⟨Set.range_eq_univ.mp hrange⟩
  have : IsIso c.i :=
    (isIso_iff_isOpenImmersion_and_surjective c.i).mpr ⟨inferInstance, inferInstance⟩
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let : c.Z.Over (Spec (.of k)) := ⟨c.g⟩
  have : c.i.IsOver (Spec (.of k)) := ⟨c.comm.symm⟩
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular C := IsRegular.of_smooth f
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : IsRegular c.Z := IsRegular.of_smooth c.g
  have : IrreducibleSpace c.Z := IsRegular.irreducibleSpace c.Z
  have : SmoothOfRelativeDimension 1 f :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := f))
  have : SmoothOfRelativeDimension 1 c.g :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq c.g 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := c.g))
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 f)
  have : SmoothOfRelativeDimension 1 (c.Z ↘ Spec (.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 c.g)
  have : IsProper (C ↘ Spec (.of k)) := inferInstanceAs (IsProper f)
  have : IsProper (c.Z ↘ Spec (.of k)) := inferInstanceAs (IsProper c.g)
  change (C ↘ Spec (.of k)).genus = (c.Z ↘ Spec (.of k)).genus
  rw [Scheme.genus_eq_arithmeticGenus (k := k) (X := C),
    Scheme.genus_eq_arithmeticGenus (k := k) (X := c.Z)]
  have := SheafOfModules.isQuasicoherent_unit (R := c.Z.ringCatSheaf)
  unfold Scheme.arithmeticGenus
  rw [← Scheme.Modules.finrankH_pullback_of_isIso c.i
    (SheafOfModules.unit c.Z.ringCatSheaf) 1]
  exact Scheme.Modules.finrankH_congr k (Scheme.Modules.pullbackObjUnitIso c.i).symm 1

private theorem proper_kummer_degree_coordinates_aux
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (n : ℕ) [NeZero n] (hn : (n : k) ≠ 0) :
    ∃ e : Sheaf.H (C.rootsOfUnitySheaf n) 2 ≃+ ZMod n,
      ∀ (hnC : IsUnit (n : Γ(C, ⊤))) (L : Additive C.Pic),
        e (C.kummerδ₁ n hnC (Scheme.Pic.toCohomologicalPicardGroupAddEquiv C L)) =
          (f.picDegree L.toMul : ZMod n) := by
  classical
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : ConnectedSpace C := IsConnectedCurve.connectedSpace (f := f)
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular C := IsRegular.of_smooth f
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := f))
  have : IsProper (C ↘ Spec (.of k)) := inferInstanceAs (IsProper f)
  let P := Scheme.Pic.toCohomologicalPicardGroupAddEquiv C
  let deg : Additive C.Pic →+ ℤ := (Scheme.picDegreeHom k C).toAdditiveLeft
  have hnC0 : IsUnit (n : Γ(C, ⊤)) := by
    simpa using hn.isUnit.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  let δ := (C.kummerδ₁ n hnC0).comp P.toAddMonoidHom
  let d : Additive C.Pic →+ ZMod n := (Int.castAddHom (ZMod n)).comp deg
  have hδ : Function.Surjective δ := by
    have := IsCurve.subsingleton_cohomologicalBrauerGroup_of_smooth f
    intro x
    obtain ⟨L, hL⟩ := ((C.exact_sheafH_rootsOfUnitySheaf_two n hnC0).2.1 x).1
      (Subsingleton.elim _ _)
    exact ⟨P.symm L, by simpa [δ] using hL⟩
  have hdeg : Function.Surjective deg := by
    intro z
    obtain ⟨L, hL⟩ := Scheme.surjective_picDegreeHom (k := k) (C := C)
      (Multiplicative.ofAdd z)
    exact ⟨Additive.ofMul L, congrArg Multiplicative.toAdd hL⟩
  have hd : Function.Surjective d := ZMod.intCast_surjective.comp hdeg
  have hker : δ.ker = d.ker := by
    ext L
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
    have hδzero : δ L = 0 ↔ ∃ M : Additive C.Pic, n • M = L := by
      change C.kummerδ₁ n hnC0 (P L) = 0 ↔ _
      rw [← AddMonoidHom.mem_ker, (C.exact_sheafH_rootsOfUnitySheaf_two n hnC0).1]
      constructor
      · rintro ⟨M, hM⟩
        refine ⟨P.symm M, ?_⟩
        apply P.injective
        simpa only [map_nsmul, AddEquiv.apply_symm_apply, zsmulAddGroupHom_apply,
          natCast_zsmul] using hM
      · rintro ⟨M, rfl⟩
        exact ⟨P M, by simp only [zsmulAddGroupHom_apply, natCast_zsmul, map_nsmul]⟩
    rw [hδzero]
    constructor
    · rintro ⟨M, rfl⟩
      simp [d, map_nsmul, nsmul_eq_mul]
    · intro hL
      obtain ⟨z, hz⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (deg L) n).mp hL
      obtain ⟨M, hM⟩ := hdeg z
      have hzero : f.picDegree (L - n • M).toMul = 0 := by
        change deg (L - n • M) = 0
        rw [map_sub, map_nsmul, hM, nsmul_eq_mul, hz, sub_self]
      obtain ⟨N, _, hN⟩ := (f.pic_proper_ntorsion_div n hn)
        (L - n • M).toMul hzero
      refine ⟨Additive.ofMul N + M, ?_⟩
      have hN' : n • Additive.ofMul N = L - n • M := by
        exact congrArg Additive.ofMul hN
      rw [smul_add, hN', sub_add_cancel]
  let e := (QuotientAddGroup.quotientKerEquivOfSurjective δ hδ).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq hker).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective d hd))
  refine ⟨e, ?_⟩
  intro hnC L
  change e (δ L) = d L
  have hmk : (QuotientAddGroup.quotientKerEquivOfSurjective δ hδ)
      (QuotientAddGroup.mk L) = δ L := rfl
  rw [← hmk]
  dsimp only [e, AddEquiv.trans_apply]
  rw [AddEquiv.symm_apply_apply]
  rfl

/-- Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance,
proof of proposition-cohomology-smooth-affine-curve, proper case in degree two
(blueprint: lem-sc-constant-proper-degree-coordinates).

Proof: a proper curve's open immersion into its smooth connected proper compactification is
proper, so its image is closed as well as open and nonempty; connectedness makes the image
all of the compactification. The immersion is an isomorphism over k and preserves genus.
Over both fields the Kummer sequence, Brauer vanishing and divisibility of Picard degree
zero identify H2(mu_n) with Pic/n and then with ZMod n by degree. Surjectivity of degree
follows from a rational point of degree one. Compose these degree identifications with the
specified primitive-root trivializations to obtain e and eK. They satisfy the displayed
boundary equations by construction. Kummer naturality and preservation of line-bundle
degree under extension give eK(r x) = e x; the Kummer boundary is surjective, so checking
this equality on its image checks every class. These maps are equivalences also for n = 1,
when both groups are zero. -/
theorem IsConnectedCurve.constant_proper_degree_coordinates
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g]
    (n : ℕ) [NeZero n] (hn : (n : k) ≠ 0)
    (r : ∀ q : ℕ, Sheaf.H (C.constantZMod n) q →+
        Sheaf.H ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).constantZMod n) q)
    (hr : (∀ q : ℕ, r q =
        (Sheaf.H.map (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).app
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))).hom) q).comp
          (Etale.cohomologyMap
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            (C.constantZMod n) q)))
    (ζ : k) (hζ : IsPrimitiveRoot ζ n)
    (hζK : IsPrimitiveRoot (algebraMap k K ζ) n)
    (t : ∀ q : ℕ, Sheaf.H (C.constantZMod n) q ≃+
          Sheaf.H (C.rootsOfUnitySheaf n) q)
        (tK : ∀ q : ℕ,
          Sheaf.H ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).constantZMod n) q ≃+
          Sheaf.H
            ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).rootsOfUnitySheaf n) q)
    (ht : (∀ q : ℕ, (t q).toAddMonoidHom =
          Sheaf.H.map (C.constantZModIsoRootsOfUnitySheaf n f hζ).hom q))
    (htK : (∀ q : ℕ, (tK q).toAddMonoidHom = Sheaf.H.map
          ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k
            K)))).constantZModIsoRootsOfUnitySheaf n
              (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) hζK).hom q))
    [IsProper f] :
    f.genus = c.g.genus ∧
    ∃ (e : Sheaf.H (C.constantZMod n) 2 ≃+ ZMod n)
            (eK : Sheaf.H
              ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).constantZMod n) 2 ≃+
                ZMod n),
            (∀ x, eK (r 2 x) = e x) ∧
            (∀ (hnC : IsUnit (n : Γ(C, ⊤))) (L : Additive C.Pic),
              e ((t 2).symm (C.kummerδ₁ n hnC
                (Scheme.Pic.toCohomologicalPicardGroupAddEquiv C L))) =
                  (f.picDegree L.toMul : ZMod n)) ∧
            (∀ (hnK : IsUnit (n : Γ(pullback f
                (Spec.map (CommRingCat.ofHom (algebraMap k K))), ⊤)))
              (L : Additive (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Pic),
              eK ((tK 2).symm
                ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).kummerδ₁ n hnK
                  (Scheme.Pic.toCohomologicalPicardGroupAddEquiv
                    (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) L))) =
                  ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).picDegree
                    L.toMul : ZMod n)) := by
  have hgenus := proper_compactification_genus_aux f c
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let D := pullback f b
  let g : D ⟶ Spec (.of K) := pullback.snd f b
  have : IsConnectedCurve g := (baseChange_curve f).2.2.2.2.2 inferInstance
  have : Smooth g := inferInstanceAs (Smooth (pullback.snd f b))
  have : IsProper g := inferInstanceAs (IsProper (pullback.snd f b))
  have hnK : (n : K) ≠ 0 := by
    simpa only [map_natCast] using
      (map_ne_zero (algebraMap k K)).mpr hn
  obtain ⟨d, hd⟩ := proper_kummer_degree_coordinates_aux f n hn
  obtain ⟨dK, hdK⟩ := proper_kummer_degree_coordinates_aux g n hnK
  let e := (t 2).trans d
  let eK := (tK 2).trans dK
  have he (hnC : IsUnit (n : Γ(C, ⊤))) (L : Additive C.Pic) :
      e ((t 2).symm (C.kummerδ₁ n hnC
        (Scheme.Pic.toCohomologicalPicardGroupAddEquiv C L))) =
          (f.picDegree L.toMul : ZMod n) := by
    simpa only [e, AddEquiv.trans_apply, AddEquiv.apply_symm_apply] using hd hnC L
  have heK (hnD : IsUnit (n : Γ(D, ⊤))) (L : Additive D.Pic) :
      eK ((tK 2).symm (D.kummerδ₁ n hnD
        (Scheme.Pic.toCohomologicalPicardGroupAddEquiv D L))) =
          (g.picDegree L.toMul : ZMod n) := by
    simpa only [eK, AddEquiv.trans_apply, AddEquiv.apply_symm_apply] using hdK hnD L
  refine ⟨hgenus, e, eK, ?_, he, heK⟩
  have hnC : IsUnit (n : Γ(C, ⊤)) := by
    simpa using hn.isUnit.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  have hnD : IsUnit (n : Γ(D, ⊤)) := by
    simpa using hnK.isUnit.map ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom
  have hnat := (constant_kummer_baseChange_naturality f c n hn
    r hr ζ hζ hζK t tK ht htK).2.1 hnC hnD
  have := IsCurve.subsingleton_cohomologicalBrauerGroup_of_smooth f
  have hsurj : Function.Surjective (C.kummerδ₁ n hnC) := by
    intro y
    exact ((C.exact_sheafH_rootsOfUnitySheaf_two n hnC).2.1 y).1
      (Subsingleton.elim _ _)
  intro x
  obtain ⟨L, hL⟩ := hsurj (t 2 x)
  let M := (Scheme.Pic.toCohomologicalPicardGroupAddEquiv C).symm L
  have hx : (t 2).symm (C.kummerδ₁ n hnC
      (Scheme.Pic.toCohomologicalPicardGroupAddEquiv C M)) = x := by
    simp only [M, AddEquiv.apply_symm_apply, hL, AddEquiv.symm_apply_apply]
  rw [← hx, hnat, heK, he]
  congr 1
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let : D.Over (Spec (.of K)) := ⟨g⟩
  have : QuasiCompact (C ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact f)
  have : QuasiSeparated (C ↘ Spec (.of k)) := inferInstanceAs (QuasiSeparated f)
  have := M.toMul.isInvertible
  rw [Scheme.Hom.picDegree_eq, Scheme.Hom.picDegree_eq]
  exact (Scheme.Modules.degree_congr K (fromSkeletonToSkeletonIso
    ((Scheme.Modules.pullback (pullback.fst f b)).obj
      ((fromSkeleton C.Modules).obj M.toMul.val)))).trans
        (Scheme.Modules.degree_pullback k K _)

end AlgebraicGeometry
