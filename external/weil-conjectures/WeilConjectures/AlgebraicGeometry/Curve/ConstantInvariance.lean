/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Affine
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.AlgebraicGeometry.Curve.PicProperNTorsion
public import WeilConjectures.AlgebraicGeometry.GenusInvariant
import WeilConjectures.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange
import WeilConjectures.AlgebraicGeometry.Curve.ConstantKummerNaturality
import WeilConjectures.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates
import WeilConjectures.AlgebraicGeometry.IsProperOrIsAffine
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.AlgebraicGeometry.BaseChangeCurve
import WeilConjectures.AlgebraicGeometry.Curve.Estimate
import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension

/-!
# Constant coefficients under algebraically closed field extension

Source: Weil conjectures blueprint, sec-curve-estimates/sbc-thm-algebraically-closed-invariance,
proposition-cohomology-smooth-affine-curve (blueprint: proposition-cohomology-smooth-affine-curve).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance,
proposition-cohomology-smooth-affine-curve (blueprint: proposition-cohomology-smooth-affine-curve).

The witness `r` is constrained to be the canonical cohomology pullback followed by the
constant-sheaf comparison. The witness `t` is the primitive-root trivialization on cohomology.
The equations for the Kummer inclusion, the units boundary, and the Picard boundary express
compatibility with Picard torsion and Picard modulo n. In the proper case the degree-two
identification is constrained by the degree of every line bundle. Compatible bases of Picard
torsion give the degree-one coordinates with the genus of the chosen compactification.
In the affine case the equations are the canonical short exact Kummer ladder, whose Picard
term is the quotient of the compactification's Jacobian described by
proposition-cohomology-smooth-affine-curve--3.

Proof following the node:
1. Use baseChange_curve for the smooth connected curve over K. Define r to be the canonical
   cohomology pullback followed by the constant-sheaf comparison. Degrees zero and one use
   constant_low_degree_baseChange_bijective. Degree two uses the proper degree coordinates or
   affine vanishing; in higher degrees both groups vanish by curve
   cohomological dimension, so r is bijective there too.
2. Apply the cohomology functor to each primitive-root sheaf isomorphism to construct t and
   tK with exactly the required underlying maps. constant_kummer_baseChange_naturality gives
   the inclusion, Picard-boundary and affine units-boundary equations.
3. For proper C, constant_proper_degree_coordinates gives degree-two coordinates and equality
   of the source and compactification genera. genus_jacobian_invariant gives the base-change
   genus equality. Proper cohomology supplies degree-one coordinates over k; composing them
   with the inverse of the bijective r in degree one supplies compatible coordinates over K.
4. Apply genus_jacobian_invariant to f when it is proper and to c.g unconditionally, retaining
   its exact classifying-morphism compatibility. Supply base-changed smoothness by
   baseChange_curve. Finally, functoriality of Picard pullback and pullback.lift_fst prove the
   affine compactification restriction equation for every line bundle. -/
theorem IsConnectedCurve.constant_cohomology_baseChange_compatible
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g]
    (n : ℕ) [NeZero n] (hn : (n : k) ≠ 0) :
    ∃ r : ∀ q : ℕ, Sheaf.H (C.constantZMod n) q →+
        Sheaf.H ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).constantZMod n) q,
      (∀ q : ℕ, r q =
        (Sheaf.H.map (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).app
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))).hom) q).comp
          (Etale.cohomologyMap
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            (C.constantZMod n) q)) ∧
      (∀ q : ℕ, Function.Bijective (r q)) ∧
      ∀ (ζ : k) (hζ : IsPrimitiveRoot ζ n)
        (hζK : IsPrimitiveRoot (algebraMap k K ζ) n),
      ∃ (t : ∀ q : ℕ, Sheaf.H (C.constantZMod n) q ≃+
          Sheaf.H (C.rootsOfUnitySheaf n) q)
        (tK : ∀ q : ℕ,
          Sheaf.H ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).constantZMod n) q ≃+
          Sheaf.H
            ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).rootsOfUnitySheaf n) q),
        (∀ q : ℕ, (t q).toAddMonoidHom =
          Sheaf.H.map (C.constantZModIsoRootsOfUnitySheaf n f hζ).hom q) ∧
        (∀ q : ℕ, (tK q).toAddMonoidHom = Sheaf.H.map
          ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k
            K)))).constantZModIsoRootsOfUnitySheaf n
              (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) hζK).hom q) ∧
        (∀ x : Sheaf.H (C.constantZMod n) 1,
          Scheme.Pic.toCohomologicalPicardGroupAddEquiv
            (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            (Additive.ofMul (Scheme.Pic.map
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
              ((Scheme.Pic.toCohomologicalPicardGroupAddEquiv C).symm
                (Sheaf.H.map (kernel.ι (n • 𝟙 C.gmSheaf)) 1 (t 1 x))).toMul)) =
          Sheaf.H.map (kernel.ι (n • 𝟙
            (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).gmSheaf)) 1
              (tK 1 (r 1 x))) ∧
        (∀ (hnC : IsUnit (n : Γ(C, ⊤)))
          (hnK : IsUnit (n : Γ(pullback f
            (Spec.map (CommRingCat.ofHom (algebraMap k K))), ⊤))) (L : Additive C.Pic),
          r 2 ((t 2).symm (C.kummerδ₁ n hnC
            (Scheme.Pic.toCohomologicalPicardGroupAddEquiv C L))) =
          (tK 2).symm
            ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).kummerδ₁ n hnK
              (Scheme.Pic.toCohomologicalPicardGroupAddEquiv
                (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
                (Additive.ofMul (Scheme.Pic.map
                  (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) L.toMul))))) ∧
        (IsProper f →
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).genus = c.g.genus ∧
          (∃ (e : Sheaf.H (C.constantZMod n) 1 ≃+ (Fin (2 * c.g.genus) → ZMod n))
            (eK : Sheaf.H
              ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).constantZMod n) 1 ≃+
                (Fin (2 * c.g.genus) → ZMod n)),
            ∀ x, eK (r 1 x) = e x) ∧
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
                    L.toMul : ZMod n))) ∧
        (∀ [IsProper f],
          ∃ (_ : GeometricallyIntegral f)
            (_ : GeometricallyIntegral
              (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
            (_ : IsConnectedCurve (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
            (_ : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))),
      ∀ (J : Over (Spec (.of k))) [GrpObj J] [IsJacobian f J]
        (e : (picardFunctorDegree f 0).obj.RepresentableBy J), IsPicardZeroMul f e →
      ∀ (JK : Over (Spec (.of K))) [GrpObj JK] [IsJacobian (pullback.snd f (Spec.map
        (CommRingCat.ofHom (algebraMap k K)))) JK]
        (eK : (picardFunctorDegree (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          0).obj.RepresentableBy JK), IsPicardZeroMul (pullback.snd f (Spec.map (CommRingCat.ofHom
          (algebraMap k K)))) eK →
      ∃ i : JK ≅ Over.mk (pullback.snd J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
      ∀ (T : Over (Spec (.of K))) (L : (pullback f (T.hom ≫ (Spec.map (CommRingCat.ofHom (algebraMap
        k K))))).Pic)
        (hL : L ∈ (picardSubfunctorDegree f 0).obj (.op ((Over.map (Spec.map (CommRingCat.ofHom
          (algebraMap k K)))).obj T))),
      ∃ hLK : Pic.map (pullbackLeftPullbackSndIso f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        T.hom).hom L ∈
          (picardSubfunctorDegree (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            0).obj (.op T),
        (eK.homEquiv.symm ((toSheafify (Scheme.fppfTopology.over (Spec (.of K)))
          (picardSubfunctorDegree (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            0).toFunctor).app (.op T)
            ⟨Pic.map (pullbackLeftPullbackSndIso f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
              T.hom).hom L, hLK⟩)).left ≫
            i.hom.left ≫ pullback.fst J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
        (e.homEquiv.symm ((toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree f 0).toFunctor).app (.op ((Over.map (Spec.map (CommRingCat.ofHom
            (algebraMap k K)))).obj T))
            ⟨L, hL⟩)).left) ∧
        (
          ∃ (_ : GeometricallyIntegral c.g)
            (_ : GeometricallyIntegral
              (pullback.snd c.g (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
            (_ : IsConnectedCurve (pullback.snd c.g (Spec.map (CommRingCat.ofHom (algebraMap k
              K)))))
            (_ : Smooth (pullback.snd c.g (Spec.map (CommRingCat.ofHom (algebraMap k K))))),
      ∀ (J : Over (Spec (.of k))) [GrpObj J] [IsJacobian c.g J]
        (e : (picardFunctorDegree c.g 0).obj.RepresentableBy J), IsPicardZeroMul c.g e →
      ∀ (JK : Over (Spec (.of K))) [GrpObj JK] [IsJacobian (pullback.snd c.g (Spec.map
        (CommRingCat.ofHom (algebraMap k K)))) JK]
        (eK : (picardFunctorDegree (pullback.snd c.g (Spec.map (CommRingCat.ofHom (algebraMap k
          K))))
          0).obj.RepresentableBy JK), IsPicardZeroMul (pullback.snd c.g (Spec.map (CommRingCat.ofHom
          (algebraMap k K)))) eK →
      ∃ i : JK ≅ Over.mk (pullback.snd J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
      ∀ (T : Over (Spec (.of K))) (L : (pullback c.g (T.hom ≫ (Spec.map (CommRingCat.ofHom
        (algebraMap
        k K))))).Pic)
        (hL : L ∈ (picardSubfunctorDegree c.g 0).obj (.op ((Over.map (Spec.map (CommRingCat.ofHom
          (algebraMap k K)))).obj T))),
      ∃ hLK : Pic.map (pullbackLeftPullbackSndIso c.g (Spec.map (CommRingCat.ofHom (algebraMap k
        K)))
        T.hom).hom L ∈
          (picardSubfunctorDegree (pullback.snd c.g (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            0).obj (.op T),
        (eK.homEquiv.symm ((toSheafify (Scheme.fppfTopology.over (Spec (.of K)))
          (picardSubfunctorDegree (pullback.snd c.g (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            0).toFunctor).app (.op T)
            ⟨Pic.map (pullbackLeftPullbackSndIso c.g (Spec.map (CommRingCat.ofHom (algebraMap k K)))
              T.hom).hom L, hLK⟩)).left ≫
            i.hom.left ≫ pullback.fst J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
        (e.homEquiv.symm ((toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree c.g 0).toFunctor).app (.op ((Over.map (Spec.map (CommRingCat.ofHom
            (algebraMap k K)))).obj T))
            ⟨L, hL⟩)).left) ∧
        (IsAffine C → ∀ (hnC : IsUnit (n : Γ(C, ⊤)))
          (hnK : IsUnit (n : Γ(pullback f
            (Spec.map (CommRingCat.ofHom (algebraMap k K))), ⊤))) (a : Additive Γ(C, ⊤)ˣ),
          r 1 ((t 1).symm (C.kummerδ₀ n hnC a)) =
          (tK 1).symm
            ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).kummerδ₀ n hnK
              (Additive.ofMul (Units.map
                (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop.hom
                a.toMul)))) ∧
        (IsAffine C → ∀ L : c.Z.Pic, L ∈ c.g.picZero →
          Scheme.Pic.map (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            (Scheme.Pic.map c.i L) =
          Scheme.Pic.map
            (pullback.map f (Spec.map (CommRingCat.ofHom (algebraMap k K))) c.g (Spec.map
              (CommRingCat.ofHom (algebraMap k K))) c.i (𝟙 _) (𝟙 _)
              ((Category.comp_id f).trans c.comm)
              ((Category.comp_id (Spec.map (CommRingCat.ofHom (algebraMap k K)))).trans
                (Category.id_comp (Spec.map (CommRingCat.ofHom (algebraMap k K)))).symm))
            (Scheme.Pic.map (pullback.fst c.g (Spec.map (CommRingCat.ofHom (algebraMap k K)))) L))
              := by
  classical
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let P := pullback f b
  let fK := pullback.snd f b
  let π := pullback.fst f b
  have hbase := baseChange_curve (k' := K) f
  have : IsConnectedCurve fK := hbase.2.2.2.2.2 inferInstance
  have : Smooth fK := hbase.2.2.1 inferInstance
  let r : ∀ q : ℕ, Sheaf.H (C.constantZMod n) q →+ Sheaf.H (P.constantZMod n) q :=
    fun q => (Sheaf.H.map
      (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} π).app
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))).hom) q).comp
          (Etale.cohomologyMap π (C.constantZMod n) q)
  have hr : ∀ q, r q = _ := fun _ => rfl
  have hlow := constant_low_degree_baseChange_bijective f c n hn r hr
  have hbij : ∀ q, Function.Bijective (r q) := by
    intro q
    by_cases hq : q ≤ 1
    · exact hlow q hq
    · by_cases hq₂ : q = 2
      · subst q
        obtain hf | hC := isProper_or_isAffine f
        · have : IsProper f := hf
          have : NeZero (n : k) := ⟨hn⟩
          obtain ⟨_, _, ζ₀, hζ₀, hmap⟩ := IsSepClosed.exists_isPrimitiveRoot k n
          let t₀ : ∀ q, Sheaf.H (C.constantZMod n) q ≃+
              Sheaf.H (C.rootsOfUnitySheaf n) q :=
            fun q => ((Sheaf.functorH C.smallEtaleTopology q).mapIso
              (C.constantZModIsoRootsOfUnitySheaf n f hζ₀)).addCommGroupIsoToAddEquiv
          let tK₀ : ∀ q, Sheaf.H (P.constantZMod n) q ≃+
              Sheaf.H (P.rootsOfUnitySheaf n) q :=
            fun q => ((Sheaf.functorH P.smallEtaleTopology q).mapIso
              (P.constantZModIsoRootsOfUnitySheaf n fK
                (hmap K (algebraMap k K)))).addCommGroupIsoToAddEquiv
          obtain ⟨_, e, eK, he, _, _⟩ := constant_proper_degree_coordinates
            f c n hn r hr ζ₀ hζ₀ (hmap K (algebraMap k K))
              t₀ tK₀ (fun _ => rfl) (fun _ => rfl)
          refine ⟨?_, ?_⟩
          · intro x y hxy
            apply e.injective
            rw [← he x, ← he y, hxy]
          · intro y
            refine ⟨e.symm (eK y), eK.injective ?_⟩
            rw [he, AddEquiv.apply_symm_apply]
        · have : IsAffine C := hC
          have : IsAffine P := hbase.2.2.2.2.1 hC
          have : Subsingleton (Sheaf.H (C.constantZMod n) 2) :=
            IsCurve.subsingleton_sheafH_two_of_isAffine f _
              (C.isTorsion_constantZMod (NeZero.ne n))
          have : Subsingleton (Sheaf.H (P.constantZMod n) 2) :=
            IsCurve.subsingleton_sheafH_two_of_isAffine fK _
              (P.isTorsion_constantZMod (NeZero.ne n))
          exact ⟨fun _ _ _ => Subsingleton.elim _ _,
            fun y => ⟨0, Subsingleton.elim _ _⟩⟩
      · have hq' : 3 ≤ q := by omega
        have : Subsingleton (Sheaf.H (C.constantZMod n) q) :=
          IsCurve.subsingleton_sheafH_of_three_le f _
            (C.isTorsion_constantZMod (NeZero.ne n)) q hq'
        have : Subsingleton (Sheaf.H (P.constantZMod n) q) :=
          IsCurve.subsingleton_sheafH_of_three_le fK _
            (P.isTorsion_constantZMod (NeZero.ne n)) q hq'
        exact ⟨fun _ _ _ => Subsingleton.elim _ _,
          fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  refine ⟨r, hr, hbij, ?_⟩
  intro ζ hζ hζK
  let t : ∀ q, Sheaf.H (C.constantZMod n) q ≃+ Sheaf.H (C.rootsOfUnitySheaf n) q :=
    fun q => ((Sheaf.functorH C.smallEtaleTopology q).mapIso
      (C.constantZModIsoRootsOfUnitySheaf n f hζ)).addCommGroupIsoToAddEquiv
  let tK : ∀ q, Sheaf.H (P.constantZMod n) q ≃+ Sheaf.H (P.rootsOfUnitySheaf n) q :=
    fun q => ((Sheaf.functorH P.smallEtaleTopology q).mapIso
      (P.constantZModIsoRootsOfUnitySheaf n fK hζK)).addCommGroupIsoToAddEquiv
  have ht : ∀ q, (t q).toAddMonoidHom = _ := fun _ => rfl
  have htK : ∀ q, (tK q).toAddMonoidHom = _ := fun _ => rfl
  obtain ⟨hpic, hboundary, hunits⟩ := constant_kummer_baseChange_naturality
    f c n hn r hr ζ hζ hζK t tK ht htK
  refine ⟨t, tK, ht, htK, hpic, hboundary, ?_, ?_, ?_, hunits, ?_⟩
  · intro hf
    have : IsProper f := hf
    obtain ⟨hgen, e₂, eK₂, he₂, hdegree, hdegreeK⟩ :=
      constant_proper_degree_coordinates f c n hn
        r hr ζ hζ hζK t tK ht htK
    obtain ⟨_, _, _, hgenK, _, _, _⟩ := genus_jacobian_invariant (K := K) f
    obtain ⟨e₁⟩ := (sheafH_constantZMod_of_isProper f n hn).2.1
    let e : Sheaf.H (C.constantZMod n) 1 ≃+ (Fin (2 * c.g.genus) → ZMod n) :=
      by
        rw [← hgen]
        exact e₁
    let er := AddEquiv.ofBijective (r 1) (hbij 1)
    refine ⟨hgenK.trans hgen, ⟨e, er.symm.trans e, ?_⟩,
      e₂, eK₂, he₂, hdegree, hdegreeK⟩
    intro x
    exact congrArg e (er.symm_apply_apply x)
  · intro hf
    have : IsProper f := hf
    obtain ⟨hGI, hCC, hGIK, _, _, _, hJ⟩ := genus_jacobian_invariant (K := K) f
    exact ⟨hGI, hGIK, hCC, inferInstance, hJ⟩
  · have : IsProper c.g := c.isProper
    obtain ⟨hGI, hCC, hGIK, _, _, _, hJ⟩ := genus_jacobian_invariant (K := K) c.g
    have : Smooth (pullback.snd c.g b) :=
      (baseChange_curve (k' := K) c.g).2.2.1 inferInstance
    exact ⟨hGI, hGIK, hCC, inferInstance, hJ⟩
  · intro _ L _
    rw [← Scheme.Pic.map_comp, ← Scheme.Pic.map_comp, pullback.lift_fst]

end AlgebraicGeometry
