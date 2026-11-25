/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.ThickeningSystemsDictionary
import WeilConjectures.AlgebraicGeometry.IdealPowerProductZeroAffineCover
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Mathlib.CategoryTheory.Whiskering

/-! # Supported thickening systems and completion isomorphisms
Source: Stacks Project, Remark 088F and Lemma 087T.
(blueprint: lem-weil-pbc-supported-thickening-dictionary).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem restriction_iso_equation
    {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {G₁ L₁ F₁ : C} {G₀ L₀ F₀ : D}
    (a : G₁ ≅ L₁) (b : G₀ ≅ L₀) (e₁ : G₁ ⟶ F₁) (e₀ : G₀ ⟶ F₀)
    (q : P.obj G₁ ≅ G₀) (φ : P.obj F₁ ≅ F₀) (d : P.obj L₁ ≅ L₀)
    (hr : q.hom ≫ b.hom = P.map a.hom ≫ d.hom)
    (he : q.hom ≫ e₀ = P.map e₁ ≫ φ.hom) :
    P.map (a.inv ≫ e₁) ≫ φ.hom = d.hom ≫ b.inv ≫ e₀ := by
  apply (cancel_epi (P.map a.hom)).1
  simp only [P.map_comp, Category.assoc]
  rw [← P.map_comp_assoc, a.hom_inv_id, P.map_id, Category.id_comp]
  calc
    _ = q.hom ≫ e₀ := he.symm
    _ = _ := by
      simpa only [Category.assoc, b.hom_inv_id_assoc] using
        congrArg (fun z ↦ z ≫ b.inv ≫ e₀) hr

/-- The annihilation and isomorphism portions of the thickening dictionary: a coherent system
`(F n, φ n)` on the thickenings whose terms are killed by the ideal of `Z` is, termwise and
compatibly with the transition maps, the system of a coherent formal module `M` supported on
`Z`; any algebraisation `G` of `M` restricts to the given system.
Source: Stacks Project, Remark 088F, Lemma 087T, and equation 0880.
(blueprint: lem-weil-pbc-supported-thickening-dictionary).
Proof: Apply the thickening-systems dictionary with the given adjunctions to the coherent system
`(F, φ)`. Its evaluation isomorphisms `β n` give the termwise isomorphisms and their transition
compatibility. At level zero, its kernel formula and the closed-immersion kernel identity
identify the displayed ideal with the kernel used by the dictionary. Evaluation isomorphisms
transport the given sectionwise annihilation to the formal terms. The affine-cover product-zero
criterion at exponent one then proves SupportedOn. Finally, invert the dictionary's completion
comparison and compose with the evaluation comparisons `r n`; their transition compatibility
gives the requested equation with the dictionary's comparison `c`, which is characterised by its
compatibility with the adjunction units. -/
theorem supportedThickening_dictionary
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ, i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))))
    (hp : ∀ n : ℕ, i n ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I :=
      I) (Nat.le_succ (n + 1))))))
    (ai : ∀ n : ℕ, Scheme.Modules.tensorPullback (i n) ⊣ Scheme.Modules.pushforward (i n))
    (aj : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) ⊣
      Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (I ^ (n + 1)))))))
    (F : ∀ n : ℕ, (pullback f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))).Modules)
    (φ : ∀ n : ℕ, (Scheme.Modules.tensorPullback (i n)).obj (F (n + 1)) ≅ F n)
    (hF : ∀ n : ℕ, RingedSpace.IsCoherent (pullback f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))).toRingedSpace (F n))
    (Z : Scheme.{u}) (j : Z ⟶ X) [IsClosedImmersion j]
    (hkill : ∀ (n : ℕ) (V : X.Opens) (a : Γ(X, V)),
        a ∈ j.ker.idealOfOpens V →
        ∀ t : Γ((Scheme.Modules.pushforward (pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj (F n), V),
          a • t = 0) :
    ∃ hX : IsNoetherian X,
      ∃ M : @CoherentFormalModule X hX
          ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f),
        @SupportedOn X Z hX
          ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f) M j _ ∧
        (∃ e : ∀ n : ℕ, M.obj.obj (Opposite.op n) ≅
            (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (I ^ (n + 1))))))).obj (F n),
          ∀ n : ℕ, M.obj.map (homOfLE (Nat.le_succ n)).op ≫ (e n).hom =
            (e (n + 1)).hom ≫
              (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).map
                ((ai n).homEquiv _ _ (φ n).hom) ≫
              (Scheme.Modules.pushforwardComp (i n) (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).hom.app (F n) ≫
              (Scheme.Modules.pushforwardCongr (hi n)).hom.app (F n)) ∧
        ∃ c : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map
            (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙
            Scheme.Modules.tensorPullback (i n) ≅
          Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))),
          (∀ (G : X.Modules) (n : ℕ),
            (aj (n + 1)).unit.app G ≫
              (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).map
                ((ai n).unit.app
                  ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                      (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj G)) ≫
              (Scheme.Modules.pushforwardComp (i n) (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).hom.app
                ((Scheme.Modules.tensorPullback (i n)).obj
                  ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                      (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj G)) ≫
              (Scheme.Modules.pushforwardCongr (hi n)).hom.app
                ((Scheme.Modules.tensorPullback (i n)).obj
                  ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                      (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj G)) ≫
              (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1))))))).map ((c n).hom.app G) =
            (aj n).unit.app G) ∧
          ∀ G : CoherentModules X,
            Nonempty ((@completion X hX
              ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f)).obj G ≅ M) →
            ∃ ψ : ∀ n : ℕ, (Scheme.Modules.tensorPullback (pullback.fst f
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G.obj ≅ F n,
              ∀ n : ℕ, (Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫
                (φ n).hom = (c n).hom.app G.obj ≫ (ψ n).hom := by
  classical
  let T (n : ℕ) := pullback f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
  let jn (n : ℕ) : T n ⟶ X := pullback.fst f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
  obtain ⟨hX, hclosed, Φ, β, _, ht, c, R, r, _, hu, hr, _, _, _, hiso, _, _⟩ :=
    thickeningSystems_dictionary f I i hi hp ai aj
  let : IsNoetherian X := hX
  have hJ : ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f) =
      (Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f := by
    have hh := (hclosed 0).2
    simp only [Nat.reduceAdd] at hh
    simp only [_root_.pow_one] at hh
    have (K : Ideal A) :
        IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion] at hh
    rw [show I ^ 1 = I from _root_.pow_one I] at hh
    exact hh
  rw [hJ]
  let S : CoherentThickeningSystem T i := ⟨F, hF, φ⟩
  refine ⟨hX, Φ.obj S, ?_, ⟨fun n ↦ (β n).app S, ht S⟩, c, hu, ?_⟩
  · change ∀ n : ℕ, IsZero (Scheme.idealModuleProduct j.ker.toModulesι
      ((Φ.obj S).obj.obj (Opposite.op n)))
    intro n
    let M := (Φ.obj S).obj.obj (Opposite.op n)
    have : M.IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X M).mp
        ((Φ.obj S).property.1 n)).1
    have hcover : ∀ x : X, ∃ U ∈ (Set.univ : Set X.affineOpens), x ∈ U.1 := by
      intro x
      obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
        (TopologicalSpace.Opens.mem_top x)
      exact ⟨⟨U, hU⟩, Set.mem_univ _, hxU⟩
    have hzero := (Scheme.idealPowerProduct_isZero_iff_affine_cover X M j.ker
      Set.univ hcover 1).mpr
    apply hzero
    intro U _ a ha
    apply Module.mem_annihilator.mpr
    intro t
    have hmem : a ∈ j.ker.idealOfOpens U.1 := by
      simpa only [_root_.pow_one, Scheme.IdealSheafData.idealOfOpens_eq_ideal] using ha
    let e : M ≅ (Scheme.Modules.pushforward (jn n)).obj (F n) := (β n).app S
    have hkill' := hkill n U.1 a hmem ((e.hom.app U.1) t)
    have hinj : Function.Injective (e.hom.app U.1) :=
      (ConcreteCategory.bijective_of_isIso (e.hom.app U.1)).1
    apply hinj
    rw [Scheme.Modules.Hom.app_smul, map_zero]
    exact hkill'
  · intro G he
    obtain ⟨ecomp⟩ := he
    obtain ⟨b, _⟩ := hiso G S
    let e : R.obj G ≅ S := b.symm ecomp
    let ψ (n : ℕ) : (Scheme.Modules.tensorPullback (jn n)).obj G.obj ≅ F n :=
      ((r n).app G).symm ≪≫ (CoherentThickeningSystem.evaluation T i n).mapIso e
    refine ⟨ψ, fun n ↦ ?_⟩
    have heq := e.hom.compatibility n
    have hres := hr G n
    change (Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫
      (φ n).hom = (c n).hom.app G.obj ≫ (ψ n).hom
    exact restriction_iso_equation (Scheme.Modules.tensorPullback (i n))
      ((r (n + 1)).app G) ((r n).app G) (e.hom.app (n + 1)) (e.hom.app n)
      ((R.obj G).comparison n) (φ n) ((c n).app G.obj) hres heq

end AlgebraicGeometry
