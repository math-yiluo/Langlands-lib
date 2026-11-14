import Langlands.AbelianScheme.Kernel
import Langlands.GroupScheme.SubgroupFunctor.CellMultiplication
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Actual kernels in compatible binary multiplication cells -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor.KernelCell

variable {S : Scheme.{u}} {G H U V P R : GroupScheme S}

/-- A commuting square of homomorphisms induces a homomorphism of the full
scheme-theoretic kernels. -/
def kernelHom (f : U ⟶ V) (q : G ⟶ H) (i : U ⟶ G) (j : V ⟶ H)
    (h : i ≫ q = f ≫ j) : kernel f ⟶ kernel q :=
  pullback.map f (kernelUnit V) q (kernelUnit H) i (𝟙 _) j h.symm
    (Subsingleton.elim _ _)

@[reassoc (attr := simp)]
theorem kernelHom_ι (f : U ⟶ V) (q : G ⟶ H) (i : U ⟶ G) (j : V ⟶ H)
    (h : i ≫ q = f ≫ j) :
    kernelHom f q i j h ≫ kernelι q = kernelι f ≫ i :=
  pullback.lift_fst _ _ _

variable (q : G ⟶ H) (f : U ⟶ V) (g : P ⟶ R)
    (i : U ⟶ G) (p : P ⟶ G) (j : V ⟶ H) (r : R ⟶ H)
    (hi : i ≫ q = f ≫ j) (hp : p ≫ q = g ≫ r)

/-- Product of the two actual kernel inclusions. -/
def inclusion : (kernel f).X ⊗ (kernel g).X ⟶ U.X ⊗ P.X :=
  (kernelι f).hom.hom ⊗ₘ (kernelι g).hom.hom

/-- Multiplication of the two induced kernel subgroups in the ambient kernel. -/
def multiplication : (kernel f).X ⊗ (kernel g).X ⟶ (kernel q).X :=
  cellMultiplication (kernelHom f q i j hi) (kernelHom g q p r hp)

@[reassoc]
theorem multiplication_ι :
    multiplication q f g i p j r hi hp ≫ (kernelι q).hom.hom =
      inclusion f g ≫ cellMultiplication i p := by
  have hf := congrArg (fun z => z.hom.hom) (kernelHom_ι f q i j hi)
  have hg := congrArg (fun z => z.hom.hom) (kernelHom_ι g q p r hp)
  simp only [Grp.comp_hom_hom] at hf hg
  simp only [multiplication, cellMultiplication, MonObj.mul_comp,
    Category.assoc, hf, hg,
    inclusion, MonObj.comp_mul, tensorHom_fst_assoc, tensorHom_snd_assoc]

include hi hp in
theorem chart_square :
    cellMultiplication i p ≫ q.hom.hom =
      (f.hom.hom ⊗ₘ g.hom.hom) ≫ cellMultiplication j r := by
  have hi' := congrArg (fun z => z.hom.hom) hi
  have hp' := congrArg (fun z => z.hom.hom) hp
  simp only [Grp.comp_hom_hom] at hi' hp'
  simp only [cellMultiplication, MonObj.mul_comp, MonObj.comp_mul,
    Category.assoc, tensorHom_fst_assoc, tensorHom_snd_assoc, hi', hp']

variable [Mono (cellMultiplication j r)]

include hi hp in
/-- If a point of the source cell maps to the unit, each of its two coordinates
maps to the unit. The target cell is only required to be monic. -/
theorem coordinates_killed {T : Over S} (a : T ⟶ U.X ⊗ P.X)
    (ha : (a ≫ cellMultiplication i p) ≫ q.hom.hom = 1) :
    (a ≫ fst U.X P.X) ≫ f.hom.hom = 1 ∧
      (a ≫ snd U.X P.X) ≫ g.hom.hom = 1 := by
  have he : a ≫ (f.hom.hom ⊗ₘ g.hom.hom) =
      lift (1 : T ⟶ V.X) (1 : T ⟶ R.X) := by
    apply (cancel_mono (cellMultiplication j r)).mp
    rw [Category.assoc, ← chart_square q f g i p j r hi hp,
      ← Category.assoc, ha, lift_cellMultiplication,
      MonObj.one_comp, MonObj.one_comp, one_mul]
  constructor
  · have h := congrArg (fun z => z ≫ fst V.X R.X) he
    simpa only [Category.assoc, tensorHom_fst, lift_fst] using h
  · have h := congrArg (fun z => z ≫ snd V.X R.X) he
    simpa only [Category.assoc, tensorHom_snd, lift_snd] using h

/-- Restricting compatible binary multiplication cells to the actual kernels
is a cartesian square of schemes over the original base. -/
theorem isPullback :
    IsPullback (inclusion f g) (multiplication q f g i p j r hi hp)
      (cellMultiplication i p) (kernelι q).hom.hom := by
  have hk (c : PullbackCone (cellMultiplication i p) (kernelι q).hom.hom) :
      (c.fst ≫ fst U.X P.X) ≫ f.hom.hom = 1 ∧
        (c.fst ≫ snd U.X P.X) ≫ g.hom.hom = 1 := by
    apply coordinates_killed q f g i p j r hi hp c.fst
    rw [c.condition, Category.assoc, (kernel_isPullback q).w]
    exact MonObj.comp_one _
  let l := fun (c : PullbackCone (cellMultiplication i p) (kernelι q).hom.hom) =>
    lift ((kernel_isPullback f).lift (c.fst ≫ fst U.X P.X) (toUnit _) (hk c).1)
      ((kernel_isPullback g).lift (c.fst ≫ snd U.X P.X) (toUnit _) (hk c).2)
  have hl (c : PullbackCone (cellMultiplication i p) (kernelι q).hom.hom) :
      l c ≫ inclusion f g = c.fst := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [l, inclusion, Category.assoc, tensorHom_fst,
        lift_fst_assoc, (kernel_isPullback f).lift_fst]
    · simp only [l, inclusion, Category.assoc, tensorHom_snd,
        lift_snd_assoc, (kernel_isPullback g).lift_fst]
  refine ⟨⟨(multiplication_ι q f g i p j r hi hp).symm⟩,
    ⟨PullbackCone.IsLimit.mk _ l hl ?_ ?_⟩⟩
  · intro c
    apply (cancel_mono (kernelι q).hom.hom).mp
    rw [Category.assoc, multiplication_ι, ← Category.assoc, hl, c.condition]
  · intro c m hm _hn
    apply CartesianMonoidalCategory.hom_ext
    · apply (cancel_mono (kernelι f).hom.hom).mp
      have h := congrArg (fun z => z ≫ fst U.X P.X) (hm.trans (hl c).symm)
      simpa only [inclusion, Category.assoc, tensorHom_fst] using h
    · apply (cancel_mono (kernelι g).hom.hom).mp
      have h := congrArg (fun z => z ≫ snd U.X P.X) (hm.trans (hl c).symm)
      simpa only [inclusion, Category.assoc, tensorHom_snd] using h

/-- An open multiplication cell induces an open multiplication cell in the
full scheme-theoretic kernel. -/
theorem isOpenImmersion_multiplication
    [IsOpenImmersion (cellMultiplication i p).left] :
    IsOpenImmersion (multiplication q f g i p j r hi hp).left := by
  have hpb : IsPullback (inclusion f g).left
      (multiplication q f g i p j r hi hp).left
      (cellMultiplication i p).left (kernelι q).hom.hom.left :=
    (isPullback q f g i p j r hi hp).map (Over.forget S)
  exact MorphismProperty.of_isPullback hpb inferInstance

end Langlands.GroupScheme.SubgroupFunctor.KernelCell
