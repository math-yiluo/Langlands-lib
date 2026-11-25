/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentThickeningSystem
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.CompletionFromRestriction
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.TensorPullback

/-! # Restriction of coherent modules and its canonical comparison with completion.

Source: Stacks Project, Cohomology of Schemes, Remark 088F and Lemma 087T.
(blueprint: lem-weil-pbc-thickening-systems-completion-comparison).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

set_option autoImplicit false

/-- Restriction of coherent modules and its canonical comparison with completion.
Source: Stacks Project, Remark 088F, Lemma 087T and equation 0880.
(blueprint: lem-weil-pbc-thickening-systems-completion-comparison).

Proof:
1. The hypotheses imply j_n and the canonical i_n are closed immersions between
   Noetherian schemes, by quotient base change and the two projection identities.
   On these schemes coherence is equivalent to quasi-coherence and finite type.
   Tensor pullback preserves finite type (finiteType_module_support_pullback).
   It preserves quasi-coherence: compare tensorPullback with the existing module
   pullback by uniqueness of left adjoints to pushforward, and apply preservation
   of quasi-coherence for that pullback. Thus j_n^* restricts to coherent modules.
2. The composite adjunction aj_(n+1).comp ai_n has right adjoint
   i_(n,*) followed by j_(n+1),*. The natural isomorphisms pushforwardComp and
   pushforwardCongr hi identify this functor with j_(n,*). Transport the adjunction
   along that isomorphism and compare its left adjoint with aj_n.left using the
   unique left-adjoint comparison. This yields c_n with precisely the first unit
   identity displayed in the theorem; this construction uses the supplied aj and ai,
   so it also covers noncanonical choices of their adjunction structures.
3. Define R.obj F to have terms j_n^* F and comparisons c_n.app F. Define R.map u
   by j_n^* u. Naturality of c_n is exactly the required compatibility equation.
   Functoriality holds componentwise. The natural evaluation isomorphisms r_n
   are the defining identifications. They give the second displayed equation.
4. For each coherent F, closedImmersion_unit_quotient for j_n identifies
   F/J^(n+1)F with j_(n,*)j_n^*F. The ideal-power construction of the quotient
   agrees with the power ideal by its affine product calculation. Transport the
   quotient identification to aj_n by the unit-normalized comparison of left
   adjoints, as in step 2, so the quotient projection becomes aj_n.unit.app F.
   Compose this quotient isomorphism with the inverse of the pushforward of r_n
   and with (β_n.app (R.obj F)).symm. Call the resulting isomorphism ρ_(F,n).
5. The htransition equation applied to R.obj F, the r_n comparison equation of
   step 3, and the unit identity of step 2 say that these termwise maps commute
   with adjacent transitions after precomposition with the quotient projection
   F → F/J^(n+2)F. This projection is epi, so cancel it to obtain compatibility.
   Every order map of natural numbers factors into adjacent maps, so the maps
   define an isomorphism of inverse systems. Naturality of quotient maps, units,
   β and r gives naturality in F, again by canceling the quotient projections.
   The coherent-formal-module category is full in inverse systems; hence these
   maps and their componentwise inverses define ρ : completion ≅ R ⋙ Φ.
   Step 4 is exactly the final displayed quotient-projection equation.
   Neither equivalence of Φ nor proper support is needed for this comparison.
-/
theorem thickeningSystems_completion_comparison {A : Type v} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A))
    [LocallyOfFiniteType f] [QuasiCompact f] (I : Ideal A)
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
        pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ,
      i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) =
          pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    (hi₂ : ∀ n : ℕ,
      i n ≫ pullback.snd f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) =
      pullback.snd f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ≫
          Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1))))))
    (ai : ∀ n : ℕ, Scheme.Modules.tensorPullback (i n) ⊣ Scheme.Modules.pushforward (i n))
    (aj : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) ⊣
      Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (I ^ (n + 1)))))))
    [hX : IsNoetherian X]
    (hgeom : (∀ n : ℕ, IsClosedImmersion (pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (I ^ (n + 1)))))) ∧
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).ker =
            (Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of
            A)).inv.hom)).comap f ^ (n + 1)))
    (Φ : CoherentThickeningSystem (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1)))))) i ⥤
          @CoherentFormalModule X hX ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso
              (CommRingCat.of A)).inv.hom)).comap f))
        (β : ∀ n : ℕ,
          Φ ⋙ ObjectProperty.ι (IsCoherentFormalModule ((Scheme.IdealSheafData.ofIdealTop (I.map
              (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)) ⋙
            (CategoryTheory.evaluation ℕᵒᵖ X.Modules).obj (op n) ≅
          CoherentThickeningSystem.evaluation (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (I ^ (n + 1)))))) i n ⋙
            Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (htransition : (∀ (M : CoherentThickeningSystem (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))) i) (n : ℕ),
          (((Φ.obj M).obj).map (homOfLE (Nat.le_succ n)).op) ≫ (β n).hom.app M =
          (β (n + 1)).hom.app M ≫
            (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).map
              ((ai n).homEquiv _ _ (M.comparison n).hom) ≫
            (Scheme.Modules.pushforwardComp (i n) (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).hom.app
              (M.term n) ≫
            (Scheme.Modules.pushforwardCongr (hi n)).hom.app (M.term n))) :
    ∃ (c : ∀ n : ℕ,
            Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙
              Scheme.Modules.tensorPullback (i n) ≅
            Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1)))))))
          (R : CoherentModules X ⥤ CoherentThickeningSystem (fun n ↦ pullback f (Spec.map
              (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) i)
          (r : ∀ n : ℕ, R ⋙ CoherentThickeningSystem.evaluation (fun n ↦ pullback f (Spec.map
              (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) i n ≅
            ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace) ⋙
              Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1)))))))
          (ρ : @completion X hX ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso
              (CommRingCat.of A)).inv.hom)).comap f) ≅ R ⋙ Φ),
          (∀ (F : X.Modules) (n : ℕ),
            (aj (n + 1)).unit.app F ≫
              (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).map
                ((ai n).unit.app
                  ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                      (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj F)) ≫
              (Scheme.Modules.pushforwardComp (i n) (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).hom.app
                ((Scheme.Modules.tensorPullback (i n)).obj
                  ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                      (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj F)) ≫
              (Scheme.Modules.pushforwardCongr (hi n)).hom.app
                ((Scheme.Modules.tensorPullback (i n)).obj
                  ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                      (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj F)) ≫
              (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1))))))).map ((c n).hom.app F) =
            (aj n).unit.app F) ∧
          (∀ (F : CoherentModules X) (n : ℕ),
            ((R.obj F).comparison n).hom ≫ (r n).hom.app F =
              (Scheme.Modules.tensorPullback (i n)).map ((r (n + 1)).hom.app F) ≫
                (c n).hom.app F.obj) ∧
          (∀ (F : CoherentModules X) (n : ℕ),
            formalModuleQuotientπ ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso
                (CommRingCat.of A)).inv.hom)).comap f) (n + 1) F.obj ≫
              (ρ.hom.app F).hom.app (op n) ≫ (β n).hom.app (R.obj F) ≫
                (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                    (Ideal.Quotient.mk (I ^ (n + 1))))))).map ((r n).hom.app F) =
            (aj n).unit.app F.obj) := by
  let j := fun n : ℕ ↦ pullback.fst f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
  let e := fun n : ℕ ↦ Scheme.Modules.pushforwardComp (i n) (j (n + 1)) ≪≫
    Scheme.Modules.pushforwardCongr (hi n)
  let a := fun n : ℕ ↦ ((aj (n + 1)).comp (ai n)).ofNatIsoRight (e n)
  let c := fun n : ℕ ↦ (a n).leftAdjointUniq (aj n)
  have hc : ∀ (F : X.Modules) (n : ℕ),
            (aj (n + 1)).unit.app F ≫
              (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).map
                ((ai n).unit.app
                  ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                      (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj F)) ≫
              (Scheme.Modules.pushforwardComp (i n) (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).hom.app
                ((Scheme.Modules.tensorPullback (i n)).obj
                  ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                      (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj F)) ≫
              (Scheme.Modules.pushforwardCongr (hi n)).hom.app
                ((Scheme.Modules.tensorPullback (i n)).obj
                  ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                      (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj F)) ≫
              (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1))))))).map ((c n).hom.app F) =
            (aj n).unit.app F := by
    intro F n
    have h := (a n).unit_leftAdjointUniq_hom_app (aj n) F
    simpa [a, e, Adjunction.comp_unit_app, Category.assoc] using h
  have hcoh (F : CoherentModules X) (n : ℕ) :
      RingedSpace.IsCoherent _ ((Scheme.Modules.tensorPullback (j n)).obj F.obj) := by
    have hj : IsClosedImmersion (j n) := (hgeom n).1
    have : IsLocallyNoetherian (pullback f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) :=
      LocallyOfFiniteType.isLocallyNoetherian (j n)
    obtain ⟨hq, ht⟩ :=
      (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F.obj).mp F.property
    have : ((Scheme.Modules.pullback (j n)).obj F.obj).IsQuasicoherent := inferInstance
    have hqc : ((Scheme.Modules.tensorPullback (j n)).obj F.obj).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent
        (pullback f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1)))))).ringCatSheaf).prop_of_iso
        (((aj n).leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction (j n))).app
          F.obj).symm inferInstance
    exact (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType _ _).mpr
      ⟨hqc, (Scheme.Modules.tensorPullback_isFiniteType _ X (j n) F.obj).1⟩
  have hext {F G : CoherentThickeningSystem
      (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
      i} (u v : CoherentThickeningSystem.Hom F G) (h : u.app = v.app) : u = v := by
    cases u
    cases v
    cases h
    rfl
  let R : CoherentModules X ⥤ CoherentThickeningSystem
      (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
      i :=
    { obj := fun F ↦
        { term := fun n ↦ (Scheme.Modules.tensorPullback (j n)).obj F.obj
          coherent := hcoh F
          comparison := fun n ↦ (c n).app F.obj }
      map := fun u ↦
        { app := fun n ↦ (Scheme.Modules.tensorPullback (j n)).map u.hom
          compatibility := fun n ↦ ((c n).hom.naturality u.hom).symm }
      map_id := by
        intro F
        apply hext
        funext n
        exact (Scheme.Modules.tensorPullback (j n)).map_id F.obj
      map_comp := by
        intro F G H u v
        apply hext
        funext n
        exact (Scheme.Modules.tensorPullback (j n)).map_comp u.hom v.hom }
  let r : ∀ n : ℕ, R ⋙ CoherentThickeningSystem.evaluation _ i n ≅
      ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace) ⋙
        Scheme.Modules.tensorPullback (j n) := fun n ↦
    NatIso.ofComponents (fun F ↦ Iso.refl _)
      (by intros; simp [R, CoherentThickeningSystem.evaluation])
  have hr : ∀ (F : CoherentModules X) (n : ℕ),
      ((R.obj F).comparison n).hom ≫ (r n).hom.app F =
        (Scheme.Modules.tensorPullback (i n)).map ((r (n + 1)).hom.app F) ≫
          (c n).hom.app F.obj := by
    intro F n
    simp [R, r, CoherentThickeningSystem.evaluation]
  obtain ⟨ρ, hρ⟩ := completion_from_restriction f I i hi hi₂ ai aj hgeom Φ β htransition
    c R r hc hr
  exact ⟨c, R, r, ρ, hc, hr, hρ⟩

end
end AlgebraicGeometry
