import Langlands.Geometry.FormalGroup.FiniteKernel

/-! # Kernel representations under formal-module isomorphisms -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ σ' τ' : Type} [Finite σ] [Finite τ] [Finite σ'] [Finite τ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'}

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace Iso

/-- The actual linear equivalence on points over a coefficient algebra. -/
def onAlgebraPoints (e : Iso M N) (A : CommAlgCat.{v} R) :
    M.AlgebraPoint A ≃ₗ[O] N.AlgebraPoint A :=
  (e.map (IsScalarTower.toAlgHom O R A)).onPoints

@[simp]
theorem onAlgebraPoints_hom_inv (e : Iso M N) (A : CommAlgCat.{v} R)
    (y : N.AlgebraPoint A) :
    e.hom.onAlgebraPoints (e.inv.onAlgebraPoints y) = y := by
  rw [← Hom.onAlgebraPoints_comp, e.hom_inv, Hom.onAlgebraPoints_id]

@[simp]
theorem onAlgebraPoints_inv_hom (e : Iso M N) (A : CommAlgCat.{v} R)
    (x : M.AlgebraPoint A) :
    e.inv.onAlgebraPoints (e.hom.onAlgebraPoints x) = x := by
  rw [← Hom.onAlgebraPoints_comp, e.inv_hom, Hom.onAlgebraPoints_id]

theorem kernelPoint_eq_zero (e : Iso M N) (A : CommAlgCat.{v} R)
    (x : e.hom.kernelPoints A) : x.val = 0 := by
  apply (e.onAlgebraPoints A).injective
  exact x.property.trans (map_zero e.hom.onAlgebraPoints).symm

/-- An isomorphism's actual kernel is represented by the base algebra itself. -/
def finiteKernelModel (e : Iso M N) : Hom.FiniteKernelModel e.hom where
  coordinateAlgebra := CommAlgCat.of R R
  finite := inferInstance
  projective := inferInstance
  represents := {
    homEquiv := {
      toFun := fun _ => ⟨0, map_zero e.hom.onAlgebraPoints⟩
      invFun := fun _ => CommAlgCat.ofHom (Algebra.ofId R _)
      left_inv := fun _ => CommAlgCat.hom_ext (Subsingleton.elim _ _)
      right_inv := fun x => by
        apply Subtype.ext
        exact (e.kernelPoint_eq_zero _ x).symm }
    homEquiv_comp := fun φ _ => by
      apply Subtype.ext
      exact (map_zero (M.algebraMapPoints φ.hom)).symm }

/-- Isomorphisms have constant kernel rank one. -/
theorem hasKernelRank_one (e : Iso M N) : e.hom.HasKernelRank 1 := by
  refine ⟨e.finiteKernelModel, fun p => ?_⟩
  let := p.nontrivial
  exact congrFun (Module.rankAtStalk_self (R := R)) p

/-- An isomorphism lifts target points over the unchanged test algebra. -/
theorem isFppfLocallySurjective (e : Iso M N) : e.hom.IsFppfLocallySurjective := by
  intro A y
  refine ⟨A, 𝟙 A, ?_, ?_, e.inv.onAlgebraPoints y, ?_⟩
  · exact RingHom.FaithfullyFlat.of_bijective Function.bijective_id
  · exact AlgHom.FinitePresentation.id R A
  · rw [onAlgebraPoints_hom_inv]
    exact (N.algebraMapPoints_id y).symm

theorem isIsogeny (e : Iso M N) : e.hom.IsIsogeny :=
  ⟨e.isFppfLocallySurjective, ⟨e.finiteKernelModel⟩⟩

/-- Isomorphisms have height zero for every chosen normalization base. -/
theorem hasHeight_zero (e : Iso M N) (q : ℕ) : e.hom.HasHeight q 0 := by
  exact ⟨e.isIsogeny, by simpa only [pow_zero] using e.hasKernelRank_one⟩

end Iso

namespace Hom

variable (f : Hom M N) (g : Hom M' N')
variable (a : Iso M M') (b : Iso N N')
variable (sq : g.comp a.hom = b.hom.comp f)

/-- The actual kernel equivalence induced by an isomorphism of arrows. -/
def kernelEquivOfIsoSquare (A : CommAlgCat.{v} R) :
    f.kernelPoints A ≃ₗ[O] g.kernelPoints A where
  toFun x := ⟨a.hom.onAlgebraPoints x.val, by
    rw [mem_kernelPoints, ← onAlgebraPoints_comp, sq, onAlgebraPoints_comp,
      x.property, map_zero]⟩
  invFun x := ⟨a.inv.onAlgebraPoints x.val, by
    apply (b.onAlgebraPoints A).injective
    change b.hom.onAlgebraPoints (f.onAlgebraPoints (a.inv.onAlgebraPoints x.val)) =
      b.hom.onAlgebraPoints 0
    rw [map_zero, ← onAlgebraPoints_comp, ← sq, onAlgebraPoints_comp,
      Iso.onAlgebraPoints_hom_inv]
    exact x.property⟩
  left_inv x := Subtype.ext (a.onAlgebraPoints_inv_hom A x.val)
  right_inv x := Subtype.ext (a.onAlgebraPoints_hom_inv A x.val)
  map_add' x y := Subtype.ext (map_add a.hom.onAlgebraPoints x.val y.val)
  map_smul' c x := Subtype.ext (map_smul a.hom.onAlgebraPoints c x.val)

/-- The kernel equivalences commute with all coefficient-algebra maps. -/
def kernelSetIsoOfIsoSquare : f.kernelSetFunctor ≅ g.kernelSetFunctor :=
  NatIso.ofComponents
    (fun A => (kernelEquivOfIsoSquare f g a b sq A).toEquiv.toIso)
    (fun φ => by
      apply ConcreteCategory.hom_ext
      intro x
      apply Subtype.ext
      exact (a.hom.onAlgebraPoints_natural φ.hom x.val).symm)

namespace FiniteKernelModel

/-- Transport a representation along an isomorphism of the actual kernel functors. -/
def transport {f : Hom M N} {g : Hom M' N'} (K : FiniteKernelModel f)
    (e : f.kernelSetFunctor ≅ g.kernelSetFunctor) : FiniteKernelModel g where
  coordinateAlgebra := K.coordinateAlgebra
  finite := K.finite
  projective := K.projective
  represents := K.represents.ofIso e

@[simp]
theorem rank_transport {f : Hom M N} {g : Hom M' N'} (K : FiniteKernelModel f)
    (e : f.kernelSetFunctor ≅ g.kernelSetFunctor) :
    (K.transport e).rank = K.rank := rfl

end FiniteKernelModel

/-- Rank conditions depend only on the actual kernel functor. -/
theorem hasKernelRank_iff_of_kernelSetIso
    (e : f.kernelSetFunctor ≅ g.kernelSetFunctor) (n : ℕ) :
    f.HasKernelRank n ↔ g.HasKernelRank n := by
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨K.transport e, hK⟩
  · rintro ⟨K, hK⟩
    exact ⟨K.transport e.symm, hK⟩

include a b sq

/-- Local lifting is preserved by an isomorphism of arrows. -/
theorem isFppfLocallySurjective_of_isoSquare (hf : f.IsFppfLocallySurjective) :
    g.IsFppfLocallySurjective := by
  intro A y
  obtain ⟨B, φ, hff, hfp, x, hx⟩ := hf A (b.inv.onAlgebraPoints y)
  refine ⟨B, φ, hff, hfp, a.hom.onAlgebraPoints x, ?_⟩
  rw [← onAlgebraPoints_comp, sq, onAlgebraPoints_comp, hx,
    ← b.hom.onAlgebraPoints_natural, b.onAlgebraPoints_hom_inv]

/-- Isogeny conditions are preserved by an isomorphism of arrows. -/
theorem isIsogeny_of_isoSquare (hf : f.IsIsogeny) : g.IsIsogeny := by
  refine ⟨isFppfLocallySurjective_of_isoSquare f g a b sq hf.1, ?_⟩
  obtain ⟨K⟩ := hf.2
  exact ⟨K.transport (kernelSetIsoOfIsoSquare f g a b sq)⟩

/-- Kernel-rank heights are preserved by an isomorphism of arrows. -/
theorem hasHeight_of_isoSquare {q h : ℕ} (hf : f.HasHeight q h) :
    g.HasHeight q h :=
  ⟨isIsogeny_of_isoSquare f g a b sq hf.1,
    (hasKernelRank_iff_of_kernelSetIso f g
      (kernelSetIsoOfIsoSquare f g a b sq) (q ^ h)).mp hf.2⟩

end Hom

end Langlands.FormalGroup.ModuleLaw
