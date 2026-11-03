import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Finite products of tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-! ### Base change of binary products -/

section BaseChange

variable {S S' : Scheme.{u}} (b : S' ⟶ S)

/-- Base change of group schemes commutes with binary products: the inverse of the monoidal
structure map of the base-change functor. -/
def baseChangeTensorIso (G H : GroupScheme S) :
    (baseChange b).obj (G ⊗ H) ≅ (baseChange b).obj G ⊗ (baseChange b).obj H :=
  (Functor.Monoidal.μIso (baseChange b) G H).symm

end BaseChange

/-! ### Finite products of group schemes -/

section Pi

variable {S : Scheme.{u}}

/-- Families on `Option α` are pairs, multiplicatively. -/
def piOptionMulEquiv {α : Type*} (M : Option α → Type*) [∀ i, Group (M i)] :
    (∀ i, M i) ≃* M none × ∀ a, M (some a) :=
  { Equiv.piOptionEquivProd with map_mul' := fun _ _ => rfl }

variable {α : Type u} [Finite α] (G : Option α → GroupScheme S)

/-- The point model of the splitting of a product over `Option α` into the factor at `none`
and the product of the remaining factors. -/
def piOptionPointsEquiv (T : Over S) :
    (T ⟶ (pi G).X) ≃* (T ⟶ (G none ⊗ pi fun a => G (some a)).X) :=
  (piPointsEquiv G T).trans ((piOptionMulEquiv _).trans
    (((MulEquiv.refl _).prodCongr (piPointsEquiv (fun a => G (some a)) T).symm).trans
      (productPointsEquiv _ _ T).symm))

/-- The two coordinates of the splitting of a product over `Option α`. -/
theorem productPointsEquiv_piOptionPointsEquiv (T : Over S) (x : T ⟶ (pi G).X) :
    productPointsEquiv _ _ T (piOptionPointsEquiv G T x) =
      (x ≫ (Pi.π G none).hom.hom, (piPointsEquiv (fun a => G (some a)) T).symm
        fun a => x ≫ (Pi.π G (some a)).hom.hom) := by
  simp only [piOptionPointsEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

theorem piOptionPointsEquiv_naturality {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ (pi G).X) :
    piOptionPointsEquiv G T' (a ≫ x) = a ≫ piOptionPointsEquiv G T x := by
  apply (productPointsEquiv (G none) (pi fun a => G (some a)) T').injective
  rw [productPointsEquiv_naturality, productPointsEquiv_piOptionPointsEquiv,
    productPointsEquiv_piOptionPointsEquiv]
  refine Prod.ext (Category.assoc _ _ _) ?_
  apply (piPointsEquiv (fun a => G (some a)) T').injective
  funext i
  simp only [piPointsEquiv_apply, Category.assoc, piPointsEquiv_symm_π]

/-- A product over `Option α` is the binary product of the factor at `none` with the product of
the remaining factors. -/
def piOptionIso : pi G ≅ G none ⊗ pi fun a => G (some a) :=
  isoOfPoints (piOptionPointsEquiv G) (piOptionPointsEquiv_naturality G)

/-- Reindexing a finite product along an equivalence of index types. -/
def piEquivIso {β : Type u} [Finite β] (e : α ≃ β) (H : β → GroupScheme S) :
    pi (fun a => H (e a)) ≅ pi H :=
  Pi.whiskerEquiv e fun _ => Iso.refl _

/-- The empty product of group schemes is the split torus of rank zero. -/
def piEmptyIso (H : PEmpty.{u + 1} → GroupScheme S) : pi H ≅ splitTorus S PEmpty :=
  Pi.whiskerEquiv (Equiv.refl _) fun i => i.elim

/-- The trivial group scheme is the split torus of rank zero. -/
def tensorUnitIso : 𝟙_ (GroupScheme S) ≅ splitTorus S PEmpty :=
  isTerminalTensorUnit.uniqueUpToIso
    (IsTerminal.ofUniqueHom (fun _ => Pi.lift fun i => i.elim)
      (fun _ _ => Pi.hom_ext _ _ fun i => i.elim))

/-- The trivial group scheme is a split torus. -/
theorem isSplitTorus_tensorUnit : IsSplitTorus (𝟙_ (GroupScheme S)) :=
  ⟨PEmpty, inferInstance, ⟨tensorUnitIso⟩⟩

end Pi

/-! ### Products of tori over a field -/

section Tori

variable {k : Type u} [Field k]

/-- The product of a split torus and a torus over a field is a torus. -/
theorem IsSplitTorus.tensor_isTorus {G H : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsSplitTorus G) (hH : IsTorus H) : IsTorus (G ⊗ H) := by
  obtain ⟨L, hL, aL, hs⟩ := hH
  exact ⟨L, hL, aL, IsSplitTorus.of_iso (baseChangeTensorIso _ G H)
    ((hG.baseChange _).tensor hs)⟩

/-- The product of two tori over a field is a torus. -/
theorem IsTorus.tensor {G H : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsTorus G) (hH : IsTorus H) : IsTorus (G ⊗ H) := by
  obtain ⟨K, hK, aK, hs⟩ := hG
  apply IsTorus.of_baseChange (K := K)
  exact IsTorus.of_iso (baseChangeTensorIso _ G H) (hs.tensor_isTorus hH.baseChange)

/-- The trivial group scheme over a field is a torus. -/
theorem isTorus_tensorUnit : IsTorus (𝟙_ (GroupScheme (Spec (CommRingCat.of k)))) :=
  isSplitTorus_tensorUnit.isTorus

/-- A finite product of tori over a field is a torus. -/
theorem IsTorus.pi {I : Type u} [Finite I] (T : I → GroupScheme (Spec (CommRingCat.of k)))
    (h : ∀ i, IsTorus (T i)) : IsTorus (GroupScheme.pi T) := by
  refine Finite.induction_empty_option
    (P := fun J => ∀ (_ : Finite J) (T : J → GroupScheme (Spec (CommRingCat.of k))),
      (∀ j, IsTorus (T j)) → IsTorus (GroupScheme.pi T)) ?_ ?_ ?_ I inferInstance T h
  · intro α β e ih _ T hT
    have : Finite α := Finite.of_equiv β e.symm
    exact IsTorus.of_iso (piEquivIso e T).symm (ih this _ fun a => hT (e a))
  · intro _ T _
    exact IsTorus.of_iso (piEmptyIso T) (isSplitTorus_splitTorus PEmpty).isTorus
  · intro α _ ih _ T hT
    exact IsTorus.of_iso (piOptionIso T)
      ((hT none).tensor (ih inferInstance _ fun a => hT (some a)))

end Tori

end Langlands.GroupScheme
