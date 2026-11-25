/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SimplicialHomObject
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# Hom objects of standard simplices and their boundaries

Source: Stacks Project, Tags 0177, 018V and 0186
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tags 0177, 018V and 0186
(auxiliary; not a blueprint node).

Proof: each degree consists of finitely many monotone maps, including constant maps.
Nondegenerate maps are exactly the injections, hence occur in only finitely many degrees.
A family on the standard simplex is determined by its identity component: compatibility
forces the component at `φ` to be that component followed by `K(φ)`. Conversely these
components are compatible by functoriality (def-weil-pbc-simplicial-hom-object and
 def-weil-pbc-simplicial-object). Evaluation at the identity gives the representing bijection.
-/
theorem simplicial_hom_standard_simplex {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (n : ℕ) :
    (∀ m : ℕ, Finite ((Δ[n] : SSet.{t}).obj (op ⦋m⦌)) ∧
      Nonempty ((Δ[n] : SSet.{t}).obj (op ⦋m⦌))) ∧
    SSet.Finite (Δ[n] : SSet.{t}) ∧
    (∀ (m : ℕ) (s : (Δ[n] : SSet.{t}).obj (op ⦋m⦌)),
      s ∈ (Δ[n] : SSet.{t}).nonDegenerate m ↔ Function.Injective s) ∧
    (∃ f : SimplicialHomFamily K (Δ[n] : SSet.{t}) (K.obj (op ⦋n⦌)),
      (∀ (m : ℕ) (s : (Δ[n] : SSet.{t}).obj (op ⦋m⦌)),
        f.val m s = K.map (SSet.stdSimplex.objEquiv s).op) ∧
      (simplicialHomFamilyFunctor K Δ[n]).IsRepresentedBy f) ∧
    (∀ (W : FormalCoproduct.{w} X.Etale) (f : SimplicialHomFamily K Δ[n] W),
      ∃! g : W ⟶ K.obj (op ⦋n⦌),
        g = f.val n (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)) ∧
        ∀ (m : ℕ) (s : (Δ[n] : SSet.{t}).obj (op ⦋m⦌)),
          f.val m s = g ≫ K.map (SSet.stdSimplex.objEquiv s).op) := by
  have hfin : ∀ m : ℕ, Finite ((Δ[n] : SSet.{t}).obj (op ⦋m⦌)) := by
    intro m
    infer_instance
  have hnon : ∀ m : ℕ, Nonempty ((Δ[n] : SSet.{t}).obj (op ⦋m⦌)) := by
    intro m
    exact ⟨SSet.stdSimplex.objEquiv.symm
      (SimplexCategory.const ⦋m⦌ ⦋n⦌ (⟨0, by omega⟩ : Fin (n + 1)))⟩
  have hnd : ∀ (m : ℕ) (s : (Δ[n] : SSet.{t}).obj (op ⦋m⦌)),
      s ∈ (Δ[n] : SSet.{t}).nonDegenerate m ↔ Function.Injective s := by
    intro m s
    rw [SSet.stdSimplex.mem_nonDegenerate_iff_mono,
      SimplexCategory.mono_iff_injective]
    rfl
  let f : SimplicialHomFamily K (Δ[n] : SSet.{t}) (K.obj (op ⦋n⦌)) :=
    ⟨fun m s ↦ K.map (SSet.stdSimplex.objEquiv s).op, by
      intro m n' φ s
      dsimp
      rw [← K.map_comp, ← op_comp]
      rfl⟩
  have hfval : ∀ (m : ℕ) (s : (Δ[n] : SSet.{t}).obj (op ⦋m⦌)),
      f.val m s = K.map (SSet.stdSimplex.objEquiv s).op := by
    intro m s
    rfl
  have hrepr : (simplicialHomFamilyFunctor K (Δ[n] : SSet.{t})).IsRepresentedBy f := by
    refine ⟨?_⟩
    intro W
    constructor
    · intro g g' h
      change SimplicialHomFamily.precomp f g = SimplicialHomFamily.precomp f g' at h
      have he := congrArg (fun q ↦ q.val n
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))) h
      dsimp [SimplicialHomFamily.precomp] at he
      simpa [f] using he
    · intro q
      let g := q.val n (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))
      refine ⟨g, ?_⟩
      apply Subtype.ext
      funext m s
      dsimp [simplicialHomFamilyFunctor, SimplicialHomFamily.precomp, f, g]
      have hq := q.property m n (SSet.stdSimplex.objEquiv s)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))
      have hs : (Δ[n] : SSet.{t}).map (SSet.stdSimplex.objEquiv s).op
          (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)) = s := by
        rw [SSet.stdSimplex.map_objEquiv_symm]
        simp
      simpa [hs] using hq
  refine ⟨fun m ↦ ⟨hfin m, hnon m⟩, inferInstance, hnd, ⟨f, hfval, hrepr⟩, ?_⟩
  intro W q
  let g := q.val n (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))
  have hq : ∀ (m : ℕ) (s : (Δ[n] : SSet.{t}).obj (op ⦋m⦌)),
      q.val m s = g ≫ K.map (SSet.stdSimplex.objEquiv s).op := by
    intro m s
    have h := q.property m n (SSet.stdSimplex.objEquiv s)
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))
    have hs : (Δ[n] : SSet.{t}).map (SSet.stdSimplex.objEquiv s).op
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)) = s := by
      rw [SSet.stdSimplex.map_objEquiv_symm]
      simp
    simpa [g, hs] using h.symm
  refine ⟨g, ⟨rfl, hq⟩, ?_⟩
  intro g' hg'
  exact hg'.1.trans rfl

private def boundaryFaceSimplex (n : ℕ) (i : Fin (n + 2)) :
    (SSet.boundary.{t} (n + 1)).toSSet.obj (op ⦋n⦌) :=
  (SSet.boundary.ι i).app (op ⦋n⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))

private theorem boundary_factor (n m : ℕ)
    (s : (SSet.boundary.{t} (n + 1)).toSSet.obj (op ⦋m⦌)) :
    ∃ (i : Fin (n + 2)) (ε : ⦋m⦌ ⟶ ⦋n⦌),
      ε ≫ SimplexCategory.δ i = SSet.stdSimplex.objEquiv s.val := by
  obtain ⟨i, ε, hε⟩ := SimplexCategory.eq_comp_δ_of_not_surjective
    (SSet.stdSimplex.objEquiv s.val) s.property
  exact ⟨i, ε, hε.symm⟩

private theorem boundary_family_factor {X : Scheme.{u}}
    {K : SimplicialObject (FormalCoproduct.{w} X.Etale)} {n : ℕ}
    {W : FormalCoproduct.{w} X.Etale}
    (f : SimplicialHomFamily K (SSet.boundary.{t} (n + 1)).toSSet W)
    (m : ℕ) (s : (SSet.boundary.{t} (n + 1)).toSSet.obj (op ⦋m⦌))
    (i : Fin (n + 2)) (ε : ⦋m⦌ ⟶ ⦋n⦌)
    (hε : ε ≫ SimplexCategory.δ i = SSet.stdSimplex.objEquiv s.val) :
    f.val m s = f.val n (boundaryFaceSimplex.{t} n i) ≫ K.map ε.op := by
  have hs : (SSet.boundary.{t} (n + 1)).toSSet.map ε.op
      (boundaryFaceSimplex.{t} n i) = s := by
    apply Subtype.ext
    apply SSet.stdSimplex.objEquiv.injective
    exact hε
  simpa only [hs] using (f.property m n ε (boundaryFaceSimplex.{t} n i)).symm

private theorem boundary_family_ext {X : Scheme.{u}}
    {K : SimplicialObject (FormalCoproduct.{w} X.Etale)} {n : ℕ}
    {W : FormalCoproduct.{w} X.Etale}
    {f g : SimplicialHomFamily K (SSet.boundary.{t} (n + 1)).toSSet W}
    (h : ∀ i, f.val n (boundaryFaceSimplex.{t} n i) =
      g.val n (boundaryFaceSimplex.{t} n i)) : f = g := by
  apply Subtype.ext
  funext m s
  obtain ⟨i, ε, hε⟩ := boundary_factor n m s
  rw [boundary_family_factor f m s i ε hε, boundary_family_factor g m s i ε hε, h]

private theorem boundary_independent_one {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale))
    {W : FormalCoproduct.{w} X.Etale} (x : Fin 2 → (W ⟶ K.obj (op ⦋0⦌)))
    (m : ℕ) (φ : ⦋m⦌ ⟶ ⦋1⦌) (i j : Fin 2) (ε ψ : ⦋m⦌ ⟶ ⦋0⦌)
    (hε : ε ≫ SimplexCategory.δ i = φ) (hψ : ψ ≫ SimplexCategory.δ j = φ) :
    x i ≫ K.map ε.op = x j ≫ K.map ψ.op := by
  have he : ε = ψ := Subsingleton.elim _ _
  have : Epi ε := SimplexCategory.epi_iff_surjective.mpr (by
    intro z
    exact ⟨0, Subsingleton.elim (α := Fin 1) _ _⟩)
  have hij : i = j := SimplexCategory.δ_injective
    ((cancel_epi ε).mp (by rw [hε, he, hψ]))
  subst j
  rw [he]

private theorem boundary_independent_lt {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (n : ℕ)
    {W : FormalCoproduct.{w} X.Etale}
    (x : Fin (n + 3) → (W ⟶ K.obj (op ⦋n + 1⦌)))
    (hx : ∀ p : (SimplicialObject.matchingBoundaryShape n).R,
      x p.val.1 ≫ (SimplicialObject.matchingBoundaryIndex K n).fst p =
        x p.val.2 ≫ (SimplicialObject.matchingBoundaryIndex K n).snd p)
    (m : ℕ) (φ : ⦋m⦌ ⟶ ⦋n + 2⦌) (i j : Fin (n + 3)) (hij : i < j)
    (ε ψ : ⦋m⦌ ⟶ ⦋n + 1⦌)
    (hε : ε ≫ SimplexCategory.δ i = φ) (hψ : ψ ≫ SimplexCategory.δ j = φ) :
    x i ≫ K.map ε.op = x j ≫ K.map ψ.op := by
  let i' : Fin (n + 2) := i.castLT (Nat.lt_of_lt_of_le hij (Nat.le_of_lt_succ j.isLt))
  let j' : Fin (n + 2) := j.pred (Fin.ne_zero_of_lt hij)
  have hδ : SimplexCategory.δ j' ≫ SimplexCategory.δ i =
      SimplexCategory.δ i' ≫ SimplexCategory.δ j := by
    exact (SimplexCategory.δ_comp_δ' (i := i') (j := j)
      (by simpa [i'] using hij)).symm
  obtain ⟨ξ, hξ⟩ := SimplexCategory.eq_comp_δ_of_not_surjective' ε j' (by
    intro z hz
    have h := congrArg (fun f ↦ f.toOrderHom z) (hε.trans hψ.symm)
    change i.succAbove (ε.toOrderHom z) = j.succAbove (ψ.toOrderHom z) at h
    rw [hz, Fin.succAbove_pred_of_lt _ _ hij] at h
    exact (Fin.ne_succAbove j (ψ.toOrderHom z)) h)
  have hψ' : ψ = ξ ≫ SimplexCategory.δ i' := by
    apply (cancel_mono (SimplexCategory.δ j)).mp
    rw [hψ, Category.assoc, ← hδ, ← Category.assoc, ← hξ, hε]
  rw [hξ, hψ']
  simp only [op_comp, K.map_comp]
  simpa only [SimplicialObject.matchingBoundaryIndex, SimplicialObject.δ,
    i', j', Category.assoc] using
    congrArg (fun f ↦ f ≫ K.map ξ.op) (hx ⟨(i, j), hij⟩)

private theorem boundary_independent {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (n : ℕ)
    {W : FormalCoproduct.{w} X.Etale}
    (x : Fin (n + 3) → (W ⟶ K.obj (op ⦋n + 1⦌)))
    (hx : ∀ p : (SimplicialObject.matchingBoundaryShape n).R,
      x p.val.1 ≫ (SimplicialObject.matchingBoundaryIndex K n).fst p =
        x p.val.2 ≫ (SimplicialObject.matchingBoundaryIndex K n).snd p)
    (m : ℕ) (φ : ⦋m⦌ ⟶ ⦋n + 2⦌) (i j : Fin (n + 3))
    (ε ψ : ⦋m⦌ ⟶ ⦋n + 1⦌)
    (hε : ε ≫ SimplexCategory.δ i = φ) (hψ : ψ ≫ SimplexCategory.δ j = φ) :
    x i ≫ K.map ε.op = x j ≫ K.map ψ.op := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact boundary_independent_lt K n x hx m φ i j hij ε ψ hε hψ
  · have : ε = ψ := (cancel_mono (SimplexCategory.δ i)).mp (hε.trans hψ.symm)
    rw [this]
  · exact (boundary_independent_lt K n x hx m φ j i hji ψ ε hψ hε).symm

private noncomputable def boundaryProjection {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) :
    (n : ℕ) → Fin (n + 2) →
      (semiRepresentableMatchingObject K (n + 1) ⟶ K.obj (op ⦋n⦌))
  | 0 => fun i ↦ Pi.π (fun _ : Fin 2 ↦ K.obj (op ⦋0⦌)) i
  | n + 1 => fun i ↦ Multiequalizer.ι (SimplicialObject.matchingBoundaryIndex K n) i

private theorem boundaryProjection_ext {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (n : ℕ)
    {W : FormalCoproduct.{w} X.Etale}
    {f g : W ⟶ semiRepresentableMatchingObject K (n + 1)}
    (h : ∀ i, f ≫ boundaryProjection K n i = g ≫ boundaryProjection K n i) : f = g := by
  cases n with
  | zero => exact Pi.hom_ext _ _ h
  | succ n => exact Multiequalizer.hom_ext _ _ _ h

private theorem boundaryProjection_independent {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (n : ℕ)
    (m : ℕ) (φ : ⦋m⦌ ⟶ ⦋n + 1⦌) (i j : Fin (n + 2)) (ε ψ : ⦋m⦌ ⟶ ⦋n⦌)
    (hε : ε ≫ SimplexCategory.δ i = φ) (hψ : ψ ≫ SimplexCategory.δ j = φ) :
    boundaryProjection K n i ≫ K.map ε.op =
      boundaryProjection K n j ≫ K.map ψ.op := by
  cases n with
  | zero => exact boundary_independent_one K (boundaryProjection K 0) m φ i j ε ψ hε hψ
  | succ n =>
    apply boundary_independent K n (boundaryProjection K (n + 1)) ?_ m φ i j ε ψ hε hψ
    intro p
    exact Multiequalizer.condition _ p

private noncomputable def boundaryUniversalFamily {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (n : ℕ) :
    SimplicialHomFamily K (SSet.boundary.{t} (n + 1)).toSSet
      (semiRepresentableMatchingObject K (n + 1)) := by
  classical
  choose i ε hε using boundary_factor.{t} n
  refine ⟨fun m s ↦ boundaryProjection K n (i m s) ≫ K.map (ε m s).op, ?_⟩
  intro m l φ s
  dsimp
  rw [Category.assoc, ← K.map_comp, ← op_comp]
  apply boundaryProjection_independent K n m _ (i l s)
    (i m ((SSet.boundary (n + 1)).toSSet.map φ.op s))
    (φ ≫ ε l s) (ε m ((SSet.boundary (n + 1)).toSSet.map φ.op s)) ?_ (hε _ _)
  rw [Category.assoc, hε]
  rfl

private theorem boundaryUniversalFamily_factor {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (n m : ℕ)
    (s : (SSet.boundary.{t} (n + 1)).toSSet.obj (op ⦋m⦌))
    (i : Fin (n + 2)) (ε : ⦋m⦌ ⟶ ⦋n⦌)
    (hε : ε ≫ SimplexCategory.δ i = SSet.stdSimplex.objEquiv s.val) :
    (boundaryUniversalFamily.{u,w,t} K n).val m s = boundaryProjection K n i ≫ K.map ε.op := by
  classical
  apply boundaryProjection_independent
  · exact (boundary_factor n m s).choose_spec.choose_spec
  · exact hε

private theorem boundaryUniversalFamily_face {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (n : ℕ) (i : Fin (n + 2)) :
    (boundaryUniversalFamily.{u,w,t} K n).val n (boundaryFaceSimplex.{t} n i) =
      boundaryProjection K n i := by
  simpa using boundaryUniversalFamily_factor K n n (boundaryFaceSimplex.{t} n i) i (𝟙 _)
    (by simp only [Category.id_comp]; rfl)

private theorem boundary_family_compatible {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (n : ℕ)
    {W : FormalCoproduct.{w} X.Etale}
    (f : SimplicialHomFamily K (SSet.boundary.{t} (n + 2)).toSSet W)
    (p : (SimplicialObject.matchingBoundaryShape n).R) :
    f.val (n + 1) (boundaryFaceSimplex (n + 1) p.val.1) ≫
        (SimplicialObject.matchingBoundaryIndex K n).fst p =
      f.val (n + 1) (boundaryFaceSimplex (n + 1) p.val.2) ≫
        (SimplicialObject.matchingBoundaryIndex K n).snd p := by
  let i : Fin (n + 2) := p.val.1.castLT
    (Nat.lt_of_lt_of_le p.property (Nat.le_of_lt_succ p.val.2.isLt))
  let j : Fin (n + 2) := p.val.2.pred (Fin.ne_zero_of_lt p.property)
  have hδ : SimplexCategory.δ j ≫ SimplexCategory.δ p.val.1 =
      SimplexCategory.δ i ≫ SimplexCategory.δ p.val.2 :=
    (SimplexCategory.δ_comp_δ' (i := i) (j := p.val.2)
      (by simpa [i] using p.property)).symm
  let s := (SSet.boundary.{t} (n + 2)).toSSet.map (SimplexCategory.δ j).op
    (boundaryFaceSimplex (n + 1) p.val.1)
  have h₁ : SimplexCategory.δ j ≫ SimplexCategory.δ p.val.1 =
      SSet.stdSimplex.objEquiv s.val := by rfl
  have h₂ : SimplexCategory.δ i ≫ SimplexCategory.δ p.val.2 =
      SSet.stdSimplex.objEquiv s.val := hδ.symm.trans h₁
  exact (boundary_family_factor f n s p.val.1 (SimplexCategory.δ j) h₁).symm.trans
    (boundary_family_factor f n s p.val.2 (SimplexCategory.δ i) h₂)

private noncomputable def boundaryFamilyLift {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (n : ℕ)
    {W : FormalCoproduct.{w} X.Etale}
    (f : SimplicialHomFamily K (SSet.boundary.{t} (n + 1)).toSSet W) :
    W ⟶ semiRepresentableMatchingObject K (n + 1) := by
  cases n with
  | zero => exact Pi.lift (fun i ↦ f.val 0 (boundaryFaceSimplex 0 i))
  | succ n =>
    exact Multiequalizer.lift (SimplicialObject.matchingBoundaryIndex K n) W
      (fun i ↦ f.val (n + 1) (boundaryFaceSimplex (n + 1) i))
      (boundary_family_compatible K n f)

private theorem boundaryFamilyLift_projection {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (n : ℕ)
    {W : FormalCoproduct.{w} X.Etale}
    (f : SimplicialHomFamily K (SSet.boundary.{t} (n + 1)).toSSet W) (i : Fin (n + 2)) :
    boundaryFamilyLift K n f ≫ boundaryProjection K n i =
      f.val n (boundaryFaceSimplex.{t} n i) := by
  cases n <;> simp [boundaryFamilyLift, boundaryProjection]

private theorem boundaryMatchingMap_projection {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (n : ℕ) (i : Fin (n + 2)) :
    semiRepresentableMatchingMap K (n + 1) ≫ boundaryProjection K n i = K.δ i := by
  cases n <;> simp [semiRepresentableMatchingMap, boundaryProjection]

/-- Source: Stacks Project, Tags 018V and 0186
(auxiliary; not a blueprint node).

Proof: in positive degree constant maps lie in the boundary, so every degree is nonempty;
its nondegenerate simplices are a subset of those of the finite standard simplex.
Restrict a boundary family to the codimension-one faces. Conversely extend a compatible
face tuple to any nonsurjective map `φ` by factoring it through a face missing from its
image (lem-weil-pbc-simplex-face-factorization). Independence of the omitted value follows
from the face identity (lem-weil-pbc-simplex-face-face-identity) and the matching equations.
Functoriality gives compatibility; restriction and extension are inverse and natural.
The matching universal property (lem-weil-pbc-simplicial-matching-object, or
lem-weil-pbc-matching-object-proper-faces) and the Hom representing property give inverse
comparison maps, and their projection equations imply uniqueness. Finally the operators
`K(φ)` give a boundary family and therefore a unique restriction morphism `ρ`.
Its composite with the comparison has projections `K(δ_i) = d_i`, exactly those of the
canonical matching map (def-weil-pbc-semi-representable-object), so they coincide.
-/
theorem simplicial_hom_boundary_matching {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (n : ℕ) :
    (∀ m : ℕ, Finite ((SSet.boundary.{t} (n + 1)).toSSet.obj (op ⦋m⦌)) ∧
      Nonempty ((SSet.boundary.{t} (n + 1)).toSSet.obj (op ⦋m⦌))) ∧
    SSet.Finite (SSet.boundary.{t} (n + 1)).toSSet ∧
    (∀ (H : FormalCoproduct.{w} X.Etale)
      (u : SimplicialHomFamily K (SSet.boundary.{t} (n + 1)).toSSet H),
      (simplicialHomFamilyFunctor K (SSet.boundary (n + 1)).toSSet).IsRepresentedBy u →
      (∃! θ : H ≅ semiRepresentableMatchingObject K (n + 1),
        ∀ i : Fin (n + 2), θ.hom ≫
          ((fun r => match r with
            | 0 => fun i => Pi.π (fun _ : Fin 2 => K.obj (op ⦋0⦌)) i
            | r + 1 => fun i =>
              Multiequalizer.ι (SimplicialObject.matchingBoundaryIndex K r) i) :
            (r : ℕ) → Fin (r + 2) →
              (semiRepresentableMatchingObject K (r + 1) ⟶ K.obj (op ⦋r⦌))) n i =
          u.val n ((SSet.boundary.ι i).app (op ⦋n⦌)
            (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)))) ∧
      (∃! ρ : K.obj (op ⦋n + 1⦌) ⟶ H,
        ∀ (m : ℕ) (s : (SSet.boundary.{t} (n + 1)).toSSet.obj (op ⦋m⦌)),
          ρ ≫ u.val m s = K.map (SSet.stdSimplex.objEquiv s.val).op) ∧
      ∀ θ : H ≅ semiRepresentableMatchingObject K (n + 1),
      (∀ i : Fin (n + 2), θ.hom ≫
          ((fun r => match r with
            | 0 => fun i => Pi.π (fun _ : Fin 2 => K.obj (op ⦋0⦌)) i
            | r + 1 => fun i =>
              Multiequalizer.ι (SimplicialObject.matchingBoundaryIndex K r) i) :
            (r : ℕ) → Fin (r + 2) →
              (semiRepresentableMatchingObject K (r + 1) ⟶ K.obj (op ⦋r⦌))) n i =
          u.val n ((SSet.boundary.ι i).app (op ⦋n⦌)
            (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)))) →
      ∀ ρ : K.obj (op ⦋n + 1⦌) ⟶ H,
        (∀ (m : ℕ) (s : (SSet.boundary.{t} (n + 1)).toSSet.obj (op ⦋m⦌)),
          ρ ≫ u.val m s = K.map (SSet.stdSimplex.objEquiv s.val).op) →
        ρ ≫ θ.hom = semiRepresentableMatchingMap K (n + 1)) := by
  classical
  refine ⟨?_, inferInstance, ?_⟩
  · intro m
    refine ⟨inferInstance, ?_⟩
    refine ⟨⟨SSet.stdSimplex.objEquiv.symm
      (SimplexCategory.const ⦋m⦌ ⦋n + 1⦌ 0), ?_⟩⟩
    change ¬Function.Surjective (fun _ : Fin (m + 1) ↦ (0 : Fin (n + 2)))
    intro h
    obtain ⟨i, hi⟩ := h ⟨1, by omega⟩
    have := congrArg Fin.val hi
    simp at this
  · intro H u hu
    let v : SimplicialHomFamily K (SSet.boundary.{t} (n + 1)).toSSet
        (semiRepresentableMatchingObject K (n + 1)) := boundaryUniversalFamily.{u,w,t} K n
    let a : H ⟶ semiRepresentableMatchingObject K (n + 1) := boundaryFamilyLift K n u
    have ha : v.precomp a = u := by
      apply boundary_family_ext
      intro i
      change a ≫ (boundaryUniversalFamily.{u,w,t} K n).val n (boundaryFaceSimplex.{t} n i) = _
      rw [boundaryUniversalFamily_face]
      exact boundaryFamilyLift_projection K n u i
    let b : semiRepresentableMatchingObject K (n + 1) ⟶ H :=
      hu.representableBy.homEquiv.symm v
    have hb : u.precomp b = v := hu.representableBy.homEquiv.apply_symm_apply v
    have hab : a ≫ b = 𝟙 H := by
      apply hu.map_bijective.1
      apply Subtype.ext
      funext m s
      change (a ≫ b) ≫ u.val m s = (𝟙 H) ≫ u.val m s
      rw [Category.assoc, Category.id_comp]
      have h₁ := congrArg (fun f ↦ f.val m s) hb
      have h₂ := congrArg (fun f ↦ f.val m s) ha
      change b ≫ u.val m s = v.val m s at h₁
      change a ≫ v.val m s = u.val m s at h₂
      rw [h₁, h₂]
    have hba : b ≫ a = 𝟙 (semiRepresentableMatchingObject K (n + 1)) := by
      apply boundaryProjection_ext K n
      intro i
      rw [Category.assoc, Category.id_comp]
      change b ≫ boundaryFamilyLift K n u ≫ boundaryProjection K n i = _
      rw [boundaryFamilyLift_projection]
      have h := congrArg (fun f ↦ f.val n (boundaryFaceSimplex.{t} n i)) hb
      change b ≫ u.val n (boundaryFaceSimplex.{t} n i) =
        (boundaryUniversalFamily.{u,w,t} K n).val n (boundaryFaceSimplex.{t} n i) at h
      simpa only [boundaryUniversalFamily_face] using h
    let e : H ≅ semiRepresentableMatchingObject K (n + 1) :=
      ⟨a, b, hab, hba⟩
    have he : ∀ i, e.hom ≫ boundaryProjection K n i =
        u.val n (boundaryFaceSimplex.{t} n i) := boundaryFamilyLift_projection K n u
    let r : SimplicialHomFamily K (SSet.boundary.{t} (n + 1)).toSSet
        (K.obj (op ⦋n + 1⦌)) :=
      ⟨fun m s ↦ K.map (SSet.stdSimplex.objEquiv s.val).op, by
        intro m l φ s
        dsimp
        rw [← K.map_comp, ← op_comp]
        rfl⟩
    let ρ : K.obj (op ⦋n + 1⦌) ⟶ H := hu.representableBy.homEquiv.symm r
    have hρ : u.precomp ρ = r := hu.representableBy.homEquiv.apply_symm_apply r
    have hρval : ∀ (m : ℕ) (s : (SSet.boundary.{t} (n + 1)).toSSet.obj (op ⦋m⦌)),
        ρ ≫ u.val m s = K.map (SSet.stdSimplex.objEquiv s.val).op := by
      intro m s
      exact congrArg (fun f ↦ f.val m s) hρ
    refine ⟨?_, ?_, ?_⟩
    · change ∃! θ : H ≅ semiRepresentableMatchingObject K (n + 1),
        ∀ i, θ.hom ≫ boundaryProjection K n i = u.val n (boundaryFaceSimplex.{t} n i)
      refine ⟨e, he, ?_⟩
      intro θ hθ
      apply Iso.ext
      apply boundaryProjection_ext K n
      intro i
      rw [hθ, he]
    · refine ⟨ρ, hρval, ?_⟩
      intro ρ' hρ'
      apply hu.map_bijective.1
      apply Subtype.ext
      funext m s
      change ρ' ≫ u.val m s = ρ ≫ u.val m s
      rw [hρ', hρval]
    · intro θ hθ ρ' hρ'
      change ∀ i, θ.hom ≫ boundaryProjection K n i =
        u.val n (boundaryFaceSimplex.{t} n i) at hθ
      apply boundaryProjection_ext K n
      intro i
      rw [Category.assoc, hθ, hρ', boundaryMatchingMap_projection]
      rfl


end AlgebraicGeometry.Scheme
