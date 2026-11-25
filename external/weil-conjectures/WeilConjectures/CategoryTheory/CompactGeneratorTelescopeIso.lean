/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import WeilConjectures.CategoryTheory.CompactHomHocolim
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.DirectSum.Module

/-!
# Recognizing a generator approximation telescope

Source: Stacks Project, Derived Categories, Tag 09SN, lemma-write-as-colimit,
proof: vanishing of the cone of the comparison map.
(blueprint: lem-pc-compact-generator-telescope-iso).
-/

@[expose] public section

universe w v u

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] [HasCoproducts.{max w v} C]

-- The Brown telescope proof, generalized from coproduct universe v to max w v.

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The comparison from a telescope to `Y` is an isomorphism if every map from a
shifted generator to `Y` lifts at stage zero and every map to a stage with zero
composite to `Y` is killed at the next stage.
Source: Stacks Project, Derived Categories, Tag 09SN, lemma-write-as-colimit,
proof: the paragraph beginning "Choose a distinguished triangle".
(blueprint: lem-pc-compact-generator-telescope-iso).

Proof: let `ι n` be the coprojection followed by `q`. Restricting the zero
composition in the telescope triangle to each summand gives `t n ≫ ι (n+1) = ι n`.
Shifts of compact objects are compact: the inverse shift equivalence preserves
coproducts, and the additive adjunction Hom equivalences identify the direct-sum
comparison with that for the unshifted object. The compact-Hom telescope theorem
(Tag 094A) and joint surjectivity of type-colimit inclusions therefore factor every
map from a shifted generator to `H` through a stage.
Postcomposition with `c` is bijective on these Hom groups. Surjectivity follows
from `hstart` and `hstage`. If a map has zero composite with `c`, factor it through
stage `n`; `hstage` gives zero composite with `f n`, so `hkill` and the telescope
relation make its image in `H` zero. Applying this to the difference of two maps
proves injectivity. Shift adjunction and the shift-addition isomorphism transport
this bijectivity to postcomposition with every target shift of `c`.
Complete `c` to `H → Y → D → H[1]`. For a map from a shifted generator to `D`,
its composite to `H[1]` is zero by injectivity for `c[1]` and consecutive-composition
vanishing. Triangle exactness factors it through `Y`; surjectivity for `c` lifts
that factor through `H`, so the original map is zero. Shift adjunction then makes
every map from `E i` to `D[n]` zero. Coproduct extensionality and `hgenerate` imply
`IsZero D`, and the triangle criterion for a zero third vertex gives `IsIso c`.
The empty generator family forces all objects zero; zero stages satisfy the same
argument. No shape assumption on the tower or compatibility hypothesis on `f`
is needed beyond the displayed `hstage` equations. -/
theorem compactGenerator_telescope_isIso
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] [HasCoproducts.{max w v} C]
    {I : Type (max w v)} (E : I → C)
    (hcompact : ∀ i : I, IsCompactObject (E i))
    (hgenerate : IsTriangulatedGeneratingFamily E)
    (Y : C) (X : ℕ → C) (t : ∀ n : ℕ, X n ⟶ X (n + 1))
    (f : ∀ n : ℕ, X n ⟶ Y)
    (hstart : ∀ (i : I) (m : ℤ) (g : (E i)⟦m⟧ ⟶ Y),
      ∃ a : (E i)⟦m⟧ ⟶ X 0, a ≫ f 0 = g)
    (hkill : ∀ (n : ℕ) (i : I) (m : ℤ) (g : (E i)⟦m⟧ ⟶ X n),
      g ≫ f n = 0 → g ≫ t n = 0)
    (H : C)
    (q : (∐ fun n : ULift.{max w v} ℕ => X n.down) ⟶ H)
    (r : H ⟶ (∐ fun n : ULift.{max w v} ℕ => X n.down)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk
      (𝟙 (∐ fun n : ULift.{max w v} ℕ => X n.down) -
        Sigma.desc (fun n : ULift.{max w v} ℕ =>
          t n.down ≫ Sigma.ι (fun k : ULift.{max w v} ℕ => X k.down)
            ⟨n.down + 1⟩)) q r ∈ distTriang C)
    (c : H ⟶ Y)
    (hstage : ∀ n : ℕ,
      Sigma.ι (fun k : ULift.{max w v} ℕ => X k.down) ⟨n⟩ ≫ q ≫ c = f n) :
    IsIso c := by
  classical
  let A := fun n : ULift.{max w v} ℕ => X n.down
  let ι : ∀ n : ℕ, X n ⟶ H := fun n => Sigma.ι A ⟨n⟩ ≫ q
  have hι (n : ℕ) : t n ≫ ι (n + 1) = ι n := by
    have hu := comp_distTriang_mor_zero₁₂ _ hT
    apply (sub_eq_zero.mp ?_).symm
    simpa [ι, A, Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, Category.id_comp] using
      congrArg (fun k => Sigma.ι A ⟨n⟩ ≫ k) hu
  have hfactor (i : I) (m : ℤ) (g : (E i)⟦m⟧ ⟶ H) :
      ∃ (n : ℕ) (a : (E i)⟦m⟧ ⟶ X n), a ≫ ι n = g := by
    let F := Functor.ofSequence t
    have hd : Triangle.mk
        (𝟙 (∐ fun n : ULift.{max w v} ℕ => F.obj n.down) -
          Sigma.desc (fun n : ULift.{max w v} ℕ =>
            F.map (homOfLE (Nat.le_succ n.down)) ≫
              Sigma.ι (fun k : ULift.{max w v} ℕ => F.obj k.down) ⟨n.down + 1⟩))
        q r ∈ distTriang C := by
      simpa [F, Functor.ofSequence, Functor.OfSequence.map_le_succ] using hT
    have hshift : IsCompactObject ((E i)⟦m⟧) := by
      intro J A
      let e := shiftEquiv C m
      have : e.functor.Additive := inferInstanceAs (shiftFunctor C m).Additive
      have : e.inverse.Additive := inferInstanceAs (shiftFunctor C (-m)).Additive
      let adj := e.toAdjunction
      let D := DirectSum.congrAddEquiv (fun j ↦ adj.homAddEquiv (E i) (A j))
      let s := sigmaComparison e.inverse A
      let post : ((E i) ⟶ e.inverse.obj (∐ A)) ≃+
          ((E i) ⟶ ∐ fun j ↦ e.inverse.obj (A j)) :=
        { toEquiv := Iso.homCongr (Iso.refl (E i)) (asIso s).symm
          map_add' := by
            intro f g
            simp [Iso.homCongr, Preadditive.add_comp] }
      let Q := (adj.homAddEquiv (E i) (∐ A)).trans post
      let φ := DirectSum.toAddMonoid
        (fun j ↦ Preadditive.rightComp (e.functor.obj (E i)) (Sigma.ι A j))
      let ψ := DirectSum.toAddMonoid
        (fun j ↦ Preadditive.rightComp (E i)
          (Sigma.ι (fun j ↦ e.inverse.obj (A j)) j))
      have hcomm : Q.toAddMonoidHom.comp φ = ψ.comp D.toAddMonoidHom := by
        apply DirectSum.addHom_ext
        intro j f
        change Q (φ (DirectSum.of _ j f)) = ψ (D (DirectSum.of _ j f))
        have hφof : φ (DirectSum.of _ j f) = f ≫ Sigma.ι A j :=
          DirectSum.toAddMonoid_of
            (fun j ↦ Preadditive.rightComp (e.functor.obj (E i)) (Sigma.ι A j)) j f
        have hDof : D (DirectSum.of _ j f) =
            DirectSum.of _ j (adj.homAddEquiv (E i) (A j) f) :=
          DirectSum.map_of
            (fun j ↦ (adj.homAddEquiv (E i) (A j)).toAddMonoidHom) j f
        rw [hφof, hDof]
        rw [show ψ (DirectSum.of _ j (adj.homAddEquiv (E i) (A j) f)) =
            adj.homAddEquiv (E i) (A j) f ≫
              Sigma.ι (fun j ↦ e.inverse.obj (A j)) j from
          DirectSum.toAddMonoid_of
            (fun j ↦ Preadditive.rightComp (E i)
              (Sigma.ι (fun j ↦ e.inverse.obj (A j)) j)) j _]
        dsimp [Q, post, Iso.homCongr]
        rw [Category.id_comp]
        change adj.homEquiv (E i) (∐ A) (f ≫ Sigma.ι A j) ≫ inv s =
          adj.homEquiv (E i) (A j) f ≫
            Sigma.ι (fun j ↦ e.inverse.obj (A j)) j
        rw [adj.homEquiv_naturality_right, Category.assoc]
        rw [map_ι_comp_inv_sigmaComparison]
      have hψ := hcompact i J (fun j ↦ e.inverse.obj (A j))
      have hφ : Function.Bijective (fun x ↦ Q (φ x)) := by
        have hh : (fun x ↦ Q (φ x)) = (fun x ↦ ψ (D x)) :=
          funext (fun x ↦ DFunLike.congr_fun hcomm x)
        rw [hh]
        exact hψ.comp D.bijective
      constructor
      · intro x y hxy
        exact hφ.1 (congrArg Q hxy)
      · intro f
        obtain ⟨x, hx⟩ := hφ.2 (Q f)
        exact ⟨x, Q.injective hx⟩
    obtain ⟨φ, hφ, hbij⟩ := compact_hom_hocolim ((E i)⟦m⟧)
      hshift F H q r hd
    obtain ⟨z, hz⟩ := hbij.2 g
    obtain ⟨n, a, ha⟩ := Types.jointly_surjective' z
    refine ⟨n, a, ?_⟩
    rw [← hz, ← ha, hφ]
    rfl
  have hbij (i : I) (m : ℤ) :
      Function.Bijective (fun a : (E i)⟦m⟧ ⟶ H => a ≫ c) := by
    have hzero (a : (E i)⟦m⟧ ⟶ H) (ha : a ≫ c = 0) : a = 0 := by
      obtain ⟨n, b, hb⟩ := hfactor i m a
      have hbf : b ≫ f n = 0 := by
        calc
          b ≫ f n = (b ≫ ι n) ≫ c := by
            simp only [ι, A, Category.assoc, hstage]
          _ = a ≫ c := by rw [hb]
          _ = 0 := ha
      rw [← hb, ← hι n, ← Category.assoc, hkill n i m b hbf, zero_comp]
    constructor
    · intro a b hab
      apply sub_eq_zero.mp
      apply hzero
      simp only [Preadditive.sub_comp, hab, sub_self]
    · intro g
      obtain ⟨a, ha⟩ := hstart i m g
      refine ⟨a ≫ ι 0, ?_⟩
      simpa only [ι, A, Category.assoc, hstage] using ha
  have hbijshift (i : I) (m n : ℤ) :
      Function.Bijective (fun a : (E i)⟦m⟧ ⟶ H⟦n⟧ => a ≫ c⟦n⟧') := by
    let K := (E i)⟦m⟧
    let adj := (shiftEquiv' C (-n) n (neg_add_cancel n)).toAdjunction
    let e : (E i)⟦m + -n⟧ ≅ K⟦-n⟧ := (shiftFunctorAdd C m (-n)).app (E i)
    have hinj (a b : K⟦-n⟧ ⟶ H) (hab : a ≫ c = b ≫ c) : a = b := by
      apply (cancel_epi e.hom).mp
      apply (hbij i (m + -n)).1
      simpa only [Category.assoc] using congrArg (fun k => e.hom ≫ k) hab
    constructor
    · intro a b hab
      apply (adj.homEquiv K H).symm.injective
      apply hinj
      have hh := congrArg (adj.homEquiv K Y).symm hab
      change (adj.homEquiv K Y).symm
        (a ≫ (shiftEquiv' C (-n) n (neg_add_cancel n)).inverse.map c) =
        (adj.homEquiv K Y).symm
          (b ≫ (shiftEquiv' C (-n) n (neg_add_cancel n)).inverse.map c) at hh
      rw [adj.homEquiv_naturality_right_symm,
        adj.homEquiv_naturality_right_symm] at hh
      exact hh
    · intro g
      obtain ⟨a, ha⟩ := (hbij i (m + -n)).2
        (e.hom ≫ (adj.homEquiv K Y).symm g)
      refine ⟨adj.homEquiv K H (e.inv ≫ a), ?_⟩
      change adj.homEquiv K H (e.inv ≫ a) ≫
        (shiftEquiv' C (-n) n (neg_add_cancel n)).inverse.map c = g
      rw [← adj.homEquiv_naturality_right]
      apply (adj.homEquiv K Y).symm.injective
      simp only [Equiv.symm_apply_apply]
      change a ≫ c = e.hom ≫ (adj.homEquiv K Y).symm g at ha
      rw [Category.assoc, ha]
      simp
  obtain ⟨D, d, δ, hd⟩ := distinguished_cocone_triangle c
  have hD (i : I) (m : ℤ) (a : (E i)⟦m⟧ ⟶ D) : a = 0 := by
    have hδ : a ≫ δ = 0 := by
      apply (hbijshift i m 1).1
      have hzero := comp_distTriang_mor_zero₃₁ _ hd
      change δ ≫ c⟦(1 : ℤ)⟧' = 0 at hzero
      simp only [Category.assoc, hzero, comp_zero, zero_comp]
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₃ _ hd a hδ
    obtain ⟨b', hb'⟩ := (hbij i m).2 b
    have hcd : c ≫ d = 0 := comp_distTriang_mor_zero₁₂ _ hd
    change a = b ≫ d at hb
    rw [hb, ← hb', Category.assoc, hcd, comp_zero]
  have hDshift (i : I) (n : ℤ) (a : E i ⟶ D⟦n⟧) : a = 0 := by
    let adj := (shiftEquiv' C (-n) n (neg_add_cancel n)).toAdjunction
    have : (shiftEquiv' C (-n) n (neg_add_cancel n)).functor.Additive :=
      inferInstanceAs (shiftFunctor C (-n)).Additive
    have : (shiftEquiv' C (-n) n (neg_add_cancel n)).inverse.Additive :=
      inferInstanceAs (shiftFunctor C n).Additive
    apply (adj.homEquiv (E i) D).symm.injective
    rw [hD i (-n) ((adj.homEquiv (E i) D).symm a)]
    exact (adj.homAddEquiv_symm_zero _ _).symm
  have hzD : IsZero D := by
    by_contra hn
    obtain ⟨n, a, ha⟩ := hgenerate D hn
    apply ha
    apply Sigma.hom_ext
    intro i
    simpa only [comp_zero] using hDshift i n (Sigma.ι E i ≫ a)
  exact (Triangle.isZero₃_iff_isIso₁ _ hd).mp hzD


end CategoryTheory
