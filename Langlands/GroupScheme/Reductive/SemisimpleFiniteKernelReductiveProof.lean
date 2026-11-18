import Langlands.GroupScheme.CentralIsogeny.CommutingLifts
import Langlands.GroupScheme.Reductive.PerfectFieldProof
import Langlands.GroupScheme.Reductive.SemisimpleRepresentationUnipotentStatement

/-! # Reductivity from a semisimple representation with finite kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A homomorphism from a smooth connected affine group is trivial if its
composite through a homomorphism with finite full kernel is trivial. -/
theorem hom_eq_one_of_finiteKernel_comp_eq_one
    {C H G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth C.X.hom] [IsAffineHom C.X.hom] [ConnectedSpace C.X.left]
    (q : H ⟶ G) [IsFinite (kernel q).X.hom] (a : C ⟶ H)
    (ha : (a ≫ q).hom.hom = 1) : a.hom.hom = 1 := by
  let d : C.X ⟶ (kernel q).X :=
    (kernelPointsEquiv q C.X).symm ⟨a.hom.hom, ha⟩
  have hd : d ≫ (kernelι q).hom.hom = a.hom.hom :=
    congrArg Subtype.val ((kernelPointsEquiv q C.X).apply_symm_apply _)
  have hd1 : η[C.X] ≫ d = η[(kernel q).X] := by
    apply (cancel_mono (kernelι q).hom.hom).mp
    rw [Category.assoc, hd, IsMonHom.one_hom, IsMonHom.one_hom]
  have hd0 : d = 1 := finiteTargetOverHom_eq_one C (kernel q) d hd1
  rw [← hd, hd0, MonObj.one_comp]

/-- The normal-unipotent action assertion implies the finite-kernel converse
of Milne's reductivity criterion over perfect fields. -/
theorem isConnectedReductive_of_semisimple_finiteKernel
    (hU : SemisimpleRepresentationUnipotentStatement.{u})
    [PerfectField k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (n : ℕ) (ρ : MatrixRepresentation G (Fin n))
    (hsem : sSup {W : Submodule k (Fin n → k) |
      ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
        ∀ U : Submodule k (Fin n → k), ρ.IsStableSubspace U → U ≤ W →
          U = ⊥ ∨ U = W} = ⊤)
    (hfin : IsFinite (kernel ρ).X.hom) : IsConnectedReductive G := by
  have hrad : HasTrivialUnipotentRadical G := by
    intro H i hi hsm hconn hun hnormal
    let : Smooth H.X.hom := hsm
    let : ConnectedSpace H.X.left := hconn
    let : IsClosedImmersion i.hom.hom.left := hi
    let : IsAffineHom H.X.hom := by
      rw [← Over.w i.hom.hom]
      infer_instance
    let : IsFinite (kernel ρ).X.hom := hfin
    have hres := (hU k G).1 H i hi hun hnormal n ρ hsem
    have hi0 : i.hom.hom = 1 :=
      hom_eq_one_of_finiteKernel_comp_eq_one ρ i
        (congrArg (fun r => r.hom.hom) hres)
    apply SubgroupFunctor.ext
    intro T
    ext x
    rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
      rw [hi0, MonObj.comp_one]
    · rintro rfl
      exact Subgroup.one_mem _
  exact (perfectFieldPseudoReductive k G).mp
    ⟨inferInstance, inferInstance, inferInstance, hrad⟩

end Langlands.GroupScheme
