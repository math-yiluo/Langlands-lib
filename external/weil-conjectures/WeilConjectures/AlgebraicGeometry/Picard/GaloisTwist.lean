/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import WeilConjectures.AlgebraicGeometry.SpecAlgebraicClosure

/-!
# The Galois action on the degree-`d` Picard functor of a geometric curve

Let `C₀` be a proper curve over a field `k`, `k̄` an algebraic closure and `C = C₀ ×_k k̄`. An
automorphism `σ` of `k̄` over `k` acts on `Pic^d_{C/k̄}`: for a scheme `T` over `k̄` let `T^σ` be
`T` with structure morphism composed with `Spec σ`; then `T` and `T^σ` are the same `k`-scheme,
and the canonical identification of `Pic^d_{C/k̄}` with the restriction of `Pic^d_{C₀/k}` to
`k̄`-schemes (`AlgebraicGeometry.picardFunctorDegreeIsoOfIsPullback`) gives a map
`σ_C^* : Pic^d_{C/k̄}(T) ⟶ Pic^d_{C/k̄}(T^σ)` (`AlgebraicGeometry.picardFunctorDegreeGaloisMap`).

If `J₀` represents `Pic^d_{C₀/k}`, then `J = J₀ ×_k k̄` represents `Pic^d_{C/k̄}` by base
change, and an endomorphism `s` of `J` over `Spec σ` and over `J₀`, such as `𝟙 × Spec σ`, induces
`σ_C^*` on the represented functor (`AlgebraicGeometry.homEquiv_galoisTwistHom`). By Yoneda, the
endomorphism of `J` over `Spec σ` inducing `σ_C^*` is unique
(`AlgebraicGeometry.eq_of_homEquiv_galoisTwistHom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- The Galois twist `T^σ` of a scheme `T` over `k̄` by a `k`-endomorphism `σ` of `k̄`: the
scheme `T` with structure morphism `T ⟶ Spec k̄ ⟶ Spec k̄`, the second map being `Spec σ`. -/
noncomputable abbrev galoisTwist (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k)
    (T : Over (Spec (.of (AlgebraicClosure k)))) : Over (Spec (.of (AlgebraicClosure k))) :=
  (Over.map (Scheme.specAlgebraicClosureMap σ).left).obj T

/-- A scheme `T` over `k̄` and its Galois twist `T^σ` are the same scheme over `k`. -/
noncomputable def galoisTwistIso (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k)
    (T : Over (Spec (.of (AlgebraicClosure k)))) :
    (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))).obj
        (galoisTwist σ T) ≅
      (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))).obj T :=
  Over.isoMk (Iso.refl _) (by
    have := Over.w (Scheme.specAlgebraicClosureMap σ)
    simp only [Scheme.specAlgebraicClosure, Over.mk_hom] at this
    simp only [Over.map_obj_hom, Iso.refl_hom, Category.id_comp, Category.assoc, this])

@[simp]
lemma galoisTwistIso_hom_left (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k)
    (T : Over (Spec (.of (AlgebraicClosure k)))) :
    (galoisTwistIso σ T).hom.left = 𝟙 T.left :=
  rfl

/-- The twist `x^σ : T^σ ⟶ J` of a `T`-point `x : T ⟶ J` along an endomorphism `s` of `J` lying
over `Spec σ`: the composite `x ≫ s`. -/
noncomputable def galoisTwistHom {σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k}
    {J : Over (Spec (.of (AlgebraicClosure k)))} (s : J.left ⟶ J.left)
    (hs : s ≫ J.hom = J.hom ≫ (Scheme.specAlgebraicClosureMap σ).left)
    {T : Over (Spec (.of (AlgebraicClosure k)))} (x : T ⟶ J) : galoisTwist σ T ⟶ J :=
  Over.homMk (x.left ≫ s) (by simp [hs])

@[simp]
lemma galoisTwistHom_left {σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k}
    {J : Over (Spec (.of (AlgebraicClosure k)))} (s : J.left ⟶ J.left)
    (hs : s ≫ J.hom = J.hom ≫ (Scheme.specAlgebraicClosureMap σ).left)
    {T : Over (Spec (.of (AlgebraicClosure k)))} (x : T ⟶ J) :
    (galoisTwistHom s hs x).left = x.left ≫ s :=
  rfl

variable {C₀ C : Scheme.{u}} [C₀.Over (Spec (.of k))] [C.Over (Spec (.of (AlgebraicClosure k)))]
  [IsProper (C₀ ↘ Spec (.of k))] [LocallyOfFinitePresentation (C₀ ↘ Spec (.of k))]
  (q : C ⟶ C₀) (h : IsPullback q (C ↘ Spec (.of (AlgebraicClosure k))) (C₀ ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) (d : ℤ)

/-- The action `σ_C^*: Pic^d_{C/k̄}(T) ⟶ Pic^d_{C/k̄}(T^σ)` of a `k`-endomorphism `σ` of `k̄`
on the degree-`d` Picard functor of the base change `C = C₀ ×_k k̄`, obtained by transport through
`Pic^d_{C₀/k}`, on which `T` and `T^σ` have the same sections
(`AlgebraicGeometry.galoisTwistIso`). -/
noncomputable def picardFunctorDegreeGaloisMap (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k)
    (T : Over (Spec (.of (AlgebraicClosure k)))) :
    (picardFunctorDegree (C ↘ Spec (.of (AlgebraicClosure k))) d).obj.obj (.op T) →
      (picardFunctorDegree (C ↘ Spec (.of (AlgebraicClosure k))) d).obj.obj
        (.op (galoisTwist σ T)) := fun y ↦
  (picardFunctorDegreeIsoOfIsPullback q h d).hom.app (.op (galoisTwist σ T))
    ((picardFunctorDegree (C₀ ↘ Spec (.of k)) d).obj.map (galoisTwistIso σ T).hom.op
      ((picardFunctorDegreeIsoOfIsPullback q h d).inv.app (.op T) y))

variable {q h d} {J₀ : Over (Spec (.of k))}
  {r : (picardFunctorDegree (C₀ ↘ Spec (.of k)) d).obj.RepresentableBy J₀}
  {rK : (picardFunctorDegree (C ↘ Spec (.of (AlgebraicClosure k))) d).obj.RepresentableBy
    (Over.mk (pullback.snd J₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))}

/-- If `rK` is the base change of the representation `r`, then the section attached by `rK` to
the point adjoint to a point `z` of `J₀` is the image of the section attached by `r` to `z`. -/
lemma homEquiv_mapPullbackAdj_homEquiv
    (hrK : ∀ (T : Over (Spec (.of (AlgebraicClosure k))))
      (y : (picardFunctorDegree (C₀ ↘ Spec (.of k)) d).obj.obj
        (.op ((Over.map (Spec.map (CommRingCat.ofHom
          (algebraMap k (AlgebraicClosure k))))).obj T))),
      rK.homEquiv.symm ((picardFunctorDegreeIsoOfIsPullback q h d).hom.app (.op T) y) =
        (Over.mapPullbackAdj _).homEquiv T J₀ (r.homEquiv.symm y))
    {T : Over (Spec (.of (AlgebraicClosure k)))}
    (z : (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))).obj T ⟶
      J₀) :
    rK.homEquiv ((Over.mapPullbackAdj _).homEquiv T J₀ z) =
      (picardFunctorDegreeIsoOfIsPullback q h d).hom.app (.op T) (r.homEquiv z) := by
  rw [← Equiv.eq_symm_apply, hrK, Equiv.symm_apply_apply]

/-- Let `J₀` represent `Pic^d_{C₀/k}` by `r` and let `J = J₀ ×_k k̄` represent `Pic^d_{C/k̄}` by
the base change `rK` of `r`. An endomorphism `s` of `J` over `J₀` and over `Spec σ`
(e.g. `𝟙 × Spec σ`) induces the Galois action `σ_C^*` on the represented functor: the
section attached to the twisted point `x ≫ s` is `σ_C^*` of the section attached to `x`. -/
theorem homEquiv_galoisTwistHom
    (hrK : ∀ (T : Over (Spec (.of (AlgebraicClosure k))))
      (y : (picardFunctorDegree (C₀ ↘ Spec (.of k)) d).obj.obj
        (.op ((Over.map (Spec.map (CommRingCat.ofHom
          (algebraMap k (AlgebraicClosure k))))).obj T))),
      rK.homEquiv.symm ((picardFunctorDegreeIsoOfIsPullback q h d).hom.app (.op T) y) =
        (Over.mapPullbackAdj _).homEquiv T J₀ (r.homEquiv.symm y))
    (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k)
    (s : pullback J₀.hom (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) ⟶
      pullback J₀.hom (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))
    (hs₁ : s ≫ pullback.fst _ _ = pullback.fst _ _)
    (hs₂ : s ≫ pullback.snd _ _ = pullback.snd _ _ ≫ (Scheme.specAlgebraicClosureMap σ).left)
    {T : Over (Spec (.of (AlgebraicClosure k)))}
    (x : T ⟶ Over.mk (pullback.snd J₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) :
    rK.homEquiv (galoisTwistHom (J := Over.mk (pullback.snd J₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) s hs₂ x) =
      picardFunctorDegreeGaloisMap q h d σ T (rK.homEquiv x) := by
  set adj := Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
    (algebraMap k (AlgebraicClosure k))))
  obtain ⟨z, rfl⟩ := (adj.homEquiv T J₀).surjective x
  have key : galoisTwistHom (J := Over.mk (pullback.snd J₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) s hs₂
        (adj.homEquiv T J₀ z) =
      adj.homEquiv (galoisTwist σ T) J₀ ((galoisTwistIso σ T).hom ≫ z) := by
    ext1
    apply pullback.hom_ext
    · simp [adj, Over.mapPullbackAdj, hs₁]
    · simp [adj, Over.mapPullbackAdj, hs₂]
  rw [key, homEquiv_mapPullbackAdj_homEquiv hrK, homEquiv_mapPullbackAdj_homEquiv hrK,
    picardFunctorDegreeGaloisMap, r.homEquiv_comp]
  congr 2
  simp

/-- An endomorphism `f` of the representing object `J` lying over `Spec σ` is determined by the
map it induces on the represented functor. -/
theorem eq_of_homEquiv_galoisTwistHom {σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k}
    {J : Over (Spec (.of (AlgebraicClosure k)))}
    {F : (Over (Spec (.of (AlgebraicClosure k))))ᵒᵖ ⥤ Type (u + 1)} (e : F.RepresentableBy J)
    {f g : J.left ⟶ J.left} (hf : f ≫ J.hom = J.hom ≫ (Scheme.specAlgebraicClosureMap σ).left)
    (hg : g ≫ J.hom = J.hom ≫ (Scheme.specAlgebraicClosureMap σ).left)
    (hfg : e.homEquiv (galoisTwistHom f hf (𝟙 J)) = e.homEquiv (galoisTwistHom g hg (𝟙 J))) :
    f = g := by
  have := congrArg CommaMorphism.left (e.homEquiv.injective hfg)
  simpa using this

/-! ### The geometric fiber of a curve -/

namespace Scheme.Hom

variable {C₀ : Scheme.{u}} (p : C₀ ⟶ Spec (.of k)) [IsProper p] [LocallyOfFinitePresentation p]
  (d : ℤ)

/-- The canonical identification of the restriction of `Pic^d_{C₀/k}` to `k̄`-schemes with
`Pic^d_{C/k̄}` for the geometric fiber `C = C₀ ×_k k̄`
(`AlgebraicGeometry.picardFunctorDegreeIsoOfIsPullback`). -/
noncomputable def geometricFiberPicardIso :
    (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))).op ⋙
        (picardFunctorDegree p d).obj ≅
      (picardFunctorDegree p.geometricFiberToAlgebraicClosure d).obj :=
  letI : C₀.Over (Spec (.of k)) := ⟨p⟩
  letI : p.geometricFiber.Over (Spec (.of (AlgebraicClosure k))) :=
    ⟨p.geometricFiberToAlgebraicClosure⟩
  haveI : IsProper (C₀ ↘ Spec (.of k)) := ‹IsProper p›
  haveI : LocallyOfFinitePresentation (C₀ ↘ Spec (.of k)) := ‹LocallyOfFinitePresentation p›
  picardFunctorDegreeIsoOfIsPullback p.geometricFiberProj (IsPullback.of_hasPullback _ _) d

/-- The action
`σ_C^*: Pic^d_{C/k̄}(T) ⟶ Pic^d_{C/k̄}(T^σ)` of `σ ∈ Gal(k̄/k)` on the degree-`d` Picard functor
of the geometric fiber `C = C₀ ×_k k̄` (`AlgebraicGeometry.picardFunctorDegreeGaloisMap`). -/
noncomputable def geometricFiberPicardGaloisMap
    (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k) (T : Over (Spec (.of (AlgebraicClosure k)))) :
    (picardFunctorDegree p.geometricFiberToAlgebraicClosure d).obj.obj (.op T) →
      (picardFunctorDegree p.geometricFiberToAlgebraicClosure d).obj.obj
        (.op (galoisTwist σ T)) :=
  letI : C₀.Over (Spec (.of k)) := ⟨p⟩
  letI : p.geometricFiber.Over (Spec (.of (AlgebraicClosure k))) :=
    ⟨p.geometricFiberToAlgebraicClosure⟩
  haveI : IsProper (C₀ ↘ Spec (.of k)) := ‹IsProper p›
  haveI : LocallyOfFinitePresentation (C₀ ↘ Spec (.of k)) := ‹LocallyOfFinitePresentation p›
  picardFunctorDegreeGaloisMap p.geometricFiberProj (IsPullback.of_hasPullback _ _) d σ T

variable {p d} {J₀ : Over (Spec (.of k))}
  {r : (picardFunctorDegree p d).obj.RepresentableBy J₀}
  {rK : (picardFunctorDegree p.geometricFiberToAlgebraicClosure d).obj.RepresentableBy
    (Over.mk J₀.hom.geometricFiberToAlgebraicClosure)}

/-- Let `J₀` represent `Pic^d_{C₀/k}` by `r`
and let `J = J₀ ×_k k̄` represent `Pic^d_{C/k̄}` by the base change `rK` of `r`. The automorphism
`σ_J = 𝟙 × Spec σ` of `J` induces the Galois action `σ_C^*` on the represented functor. -/
theorem homEquiv_galoisTwistHom_geometricFiberGaloisMap
    (hrK : ∀ (T : Over (Spec (.of (AlgebraicClosure k))))
      (y : (picardFunctorDegree p d).obj.obj
        (.op ((Over.map (Spec.map (CommRingCat.ofHom
          (algebraMap k (AlgebraicClosure k))))).obj T))),
      rK.homEquiv.symm ((p.geometricFiberPicardIso d).hom.app (.op T) y) =
        (Over.mapPullbackAdj _).homEquiv T J₀ (r.homEquiv.symm y))
    (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k) {T : Over (Spec (.of (AlgebraicClosure k)))}
    (x : T ⟶ Over.mk J₀.hom.geometricFiberToAlgebraicClosure) :
    rK.homEquiv (galoisTwistHom (J₀.hom.geometricFiberGaloisMap σ)
      (J₀.hom.geometricFiberGaloisMap_comp_geometricFiberToAlgebraicClosure σ) x) =
      p.geometricFiberPicardGaloisMap d σ T (rK.homEquiv x) :=
  letI : C₀.Over (Spec (.of k)) := ⟨p⟩
  letI : p.geometricFiber.Over (Spec (.of (AlgebraicClosure k))) :=
    ⟨p.geometricFiberToAlgebraicClosure⟩
  haveI : IsProper (C₀ ↘ Spec (.of k)) := ‹IsProper p›
  haveI : LocallyOfFinitePresentation (C₀ ↘ Spec (.of k)) := ‹LocallyOfFinitePresentation p›
  homEquiv_galoisTwistHom (q := p.geometricFiberProj) (h := IsPullback.of_hasPullback _ _)
    (r := r) (rK := rK) hrK σ (J₀.hom.geometricFiberGaloisMap σ)
    (J₀.hom.geometricFiberGaloisMap_comp_geometricFiberProj σ)
    (J₀.hom.geometricFiberGaloisMap_comp_geometricFiberToAlgebraicClosure σ) x


/-- In the situation of
`AlgebraicGeometry.Scheme.Hom.homEquiv_galoisTwistHom_geometricFiberGaloisMap`, the automorphism
`σ_J = 𝟙 × Spec σ` is the unique endomorphism of `J` lying over `Spec σ` which induces the Galois
action `σ_C^*` on the represented functor. -/
theorem homEquiv_galoisTwistHom_iff
    (hrK : ∀ (T : Over (Spec (.of (AlgebraicClosure k))))
      (y : (picardFunctorDegree p d).obj.obj
        (.op ((Over.map (Spec.map (CommRingCat.ofHom
          (algebraMap k (AlgebraicClosure k))))).obj T))),
      rK.homEquiv.symm ((p.geometricFiberPicardIso d).hom.app (.op T) y) =
        (Over.mapPullbackAdj _).homEquiv T J₀ (r.homEquiv.symm y))
    (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k)
    (f : J₀.hom.geometricFiber ⟶ J₀.hom.geometricFiber)
    (hf : f ≫ J₀.hom.geometricFiberToAlgebraicClosure =
      J₀.hom.geometricFiberToAlgebraicClosure ≫ (Scheme.specAlgebraicClosureMap σ).left) :
    (∀ (T : Over (Spec (.of (AlgebraicClosure k))))
      (x : T ⟶ Over.mk J₀.hom.geometricFiberToAlgebraicClosure),
      rK.homEquiv (galoisTwistHom (J := Over.mk J₀.hom.geometricFiberToAlgebraicClosure)
        f hf x) = p.geometricFiberPicardGaloisMap d σ T (rK.homEquiv x)) ↔
      f = J₀.hom.geometricFiberGaloisMap σ := by
  constructor
  · intro H
    refine eq_of_homEquiv_galoisTwistHom rK hf
      (J₀.hom.geometricFiberGaloisMap_comp_geometricFiberToAlgebraicClosure σ) ?_
    rw [H, homEquiv_galoisTwistHom_geometricFiberGaloisMap hrK]
  · rintro rfl T x
    exact homEquiv_galoisTwistHom_geometricFiberGaloisMap hrK σ x

end Scheme.Hom

end AlgebraicGeometry
