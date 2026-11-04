import Langlands.GroupScheme.HopfPrimitiveQuotient
import Langlands.GroupScheme.AffineQuotientStatement
import Langlands.GroupScheme.AffineHomImage
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.DominantHomFlatProof
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.ReducedSubgroup
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveAffineDescentProof
import Langlands.AlgebraicGeometry.FieldExtensionAffineDescentProof

/-! # Reduction of the affine quotient theorem to exact-kernel representations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineQuotient

/-- Every normal closed subgroup of a smooth affine group of finite type over an algebraically
closed field is the scheme-theoretic kernel of a finite-dimensional representation. -/
def SmoothNormalKernelInput : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
      IsClosedSubgroup i → (SubgroupFunctor.range i).IsNormal →
        ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
          SubgroupFunctor.range (kernelι ρ) = SubgroupFunctor.range i

section Kernel

variable {S : Scheme.{u}} {G H H' : GroupScheme S}

/-- A homomorphism kills the kernel of `q` once that kernel lies in its own kernel. -/
theorem kernelι_comp_eq_zero {q : G ⟶ H} {f : G ⟶ H'}
    (h : SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range (kernelι f)) :
    kernelι q ≫ f = 0 := by
  have hx : (kernelι q).hom.hom ∈ (SubgroupFunctor.range (kernelι q)).carrier (kernel q).X :=
    SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  have h1 := (mem_range_kernelι_iff f _).mp (h _ hx)
  apply Grp.hom_ext
  rw [Grp.comp_hom_hom, h1]
  rfl

/-- The kernel of a homomorphism lies in the kernel of each of its composites. -/
theorem range_kernelι_le_of_comp_eq {p : G ⟶ H} {i : H ⟶ H'} {f : G ⟶ H'}
    (hf : p ≫ i = f) :
    SubgroupFunctor.range (kernelι p) ≤ SubgroupFunctor.range (kernelι f) := by
  intro T x hx
  rw [mem_range_kernelι_iff] at hx ⊢
  rw [← hf, Grp.comp_hom_hom, ← Category.assoc, hx, MonObj.one_comp]

/-- Composing with a monomorphism does not change the kernel. -/
theorem range_kernelι_le_of_comp_eq_mono {p : G ⟶ H} {i : H ⟶ H'} {f : G ⟶ H'}
    [Mono i.hom.hom] (hf : p ≫ i = f) :
    SubgroupFunctor.range (kernelι f) ≤ SubgroupFunctor.range (kernelι p) := by
  intro T x hx
  rw [mem_range_kernelι_iff] at hx ⊢
  apply (cancel_mono i.hom.hom).mp
  rw [Category.assoc, ← Grp.comp_hom_hom, hf, hx, MonObj.one_comp]

end Kernel

section Smooth

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **Smooth case.** Over an algebraically closed field, a flat surjective quasi-compact
homomorphism from a smooth affine group of finite type has affine target, given exact-kernel
representations of normal closed subgroups. -/
theorem isAffineHom_of_smooth (hN : SmoothNormalKernelInput.{u})
    (G Q : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] [Smooth G.X.hom]
    [IsSeparated Q.X.hom]
    (q : G ⟶ Q) [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left] :
    IsAffineHom Q.X.hom := by
  obtain ⟨n, ρ, hρ⟩ := hN k G (kernel q) (kernelι q)
    (kernelι_isClosedImmersion q) (HopfPrimitive.isNormal_range_kernelι q)
  have : Smooth (GeneralLinear.groupScheme (Fin n) (CommRingCat.of k)).X.hom :=
    GeneralLinear.smoothStatement (Fin n) _
  have : IsAffineHom (GeneralLinear.groupScheme (Fin n) (CommRingCat.of k)).X.hom :=
    GeneralLinear.isAffineHom_groupScheme _ _
  have : Smooth (AffineHomImage.image ρ).X.hom := AffineHomImage.smooth_image ρ
  have : IsReduced (AffineHomImage.image ρ).X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ (AffineHomImage.image ρ).X.hom
  have : QuasiCompact (AffineHomImage.projection ρ).hom.hom.left :=
    inferInstanceAs (QuasiCompact (AffineHomImage.projectionOver ρ).left)
  have : IsDominant (AffineHomImage.projection ρ).hom.hom.left := inferInstance
  obtain ⟨hpf, hps, hpq⟩ := dominantGroupHomFlat k G (AffineHomImage.image ρ)
    (AffineHomImage.projection ρ)
  have : Mono (AffineHomImage.inclusion ρ).hom.hom :=
    inferInstanceAs (Mono (AffineHomImage.inclusionOver ρ))
  have hk1 : kernelι q ≫ AffineHomImage.projection ρ = 0 :=
    kernelι_comp_eq_zero (hρ.symm.le.trans
      (range_kernelι_le_of_comp_eq_mono (AffineHomImage.projection_inclusion ρ)))
  have hk2 : kernelι (AffineHomImage.projection ρ) ≫ q = 0 :=
    kernelι_comp_eq_zero
      ((range_kernelι_le_of_comp_eq (AffineHomImage.projection_inclusion ρ)).trans hρ.le)
  have hk0 : kernelι q ≫ q = 0 := kernelι_comp_eq_zero le_rfl
  let h : Q ⟶ AffineHomImage.image ρ := FpqcHomDescent.hom q _ hk1
  let h' : AffineHomImage.image ρ ⟶ Q := FpqcHomDescent.hom _ q hk2
  have hk0' : kernelι (AffineHomImage.projection ρ) ≫ AffineHomImage.projection ρ = 0 :=
    kernelι_comp_eq_zero le_rfl
  have e1 : h ≫ h' = 𝟙 Q :=
    (FpqcHomDescent.unique q q hk0 _ (by
        rw [FpqcHomDescent.fac_assoc, FpqcHomDescent.fac])).trans
      (FpqcHomDescent.unique q q hk0 _ (Category.comp_id q)).symm
  have e2 : h' ≫ h = 𝟙 _ :=
    (FpqcHomDescent.unique _ _ hk0' _ (by
        rw [FpqcHomDescent.fac_assoc, FpqcHomDescent.fac])).trans
      (FpqcHomDescent.unique _ _ hk0' _ (Category.comp_id _)).symm
  have : IsIso h.hom.hom.left :=
    ⟨⟨h'.hom.hom.left, congrArg (fun x => x.hom.hom.left) e1,
      congrArg (fun x => x.hom.hom.left) e2⟩⟩
  rw [← Over.w h.hom.hom]
  infer_instance

end Smooth

section Reduced

/-- Affineness descends along a finite surjective morphism of schemes over a common base. This
is the published finite-surjective affine descent for algebraic spaces, applied to schemes. -/
theorem isAffine_of_finite_surjective {S : Scheme.{u}} {U V : Over S} (f : V ⟶ U)
    (hf : IsFinite f.left) (hs : Surjective f.left) [IsAffine V.left] : IsAffine U.left := by
  let _ : (MorphismProperty.inverseImage (@IsFinite.{u}) (Over.forget S)).IsStableUnderBaseChange :=
    { of_isPullback := fun sq hg ↦
        MorphismProperty.of_isPullback (P := @IsFinite.{u}) (sq.map (Over.forget S)) hg }
  let _ : (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).IsStableUnderBaseChange :=
    { of_isPullback := fun sq hg ↦
        MorphismProperty.of_isPullback (P := @Surjective.{u}) (sq.map (Over.forget S)) hg }
  have hfin : Langlands.AlgebraicGeometry.AlgebraicSpace.IsFinite
      (Langlands.AlgebraicGeometry.AlgebraicSpace.hom
        ((Langlands.AlgebraicGeometry.AlgebraicSpace.schemeToSpace S).map f)) :=
    MorphismProperty.relative_map
      (F := Langlands.AlgebraicGeometry.AlgebraicSpace.schemeYoneda S)
      (P := MorphismProperty.inverseImage (@IsFinite.{u}) (Over.forget S)) hf
  have hsurj : Langlands.AlgebraicGeometry.AlgebraicSpace.IsSurjective
      (Langlands.AlgebraicGeometry.AlgebraicSpace.hom
        ((Langlands.AlgebraicGeometry.AlgebraicSpace.schemeToSpace S).map f)) :=
    MorphismProperty.relative_map
      (F := Langlands.AlgebraicGeometry.AlgebraicSpace.schemeYoneda S)
      (P := MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)) hs
  obtain ⟨W, hW, ⟨e⟩⟩ :=
    Langlands.AlgebraicGeometry.AlgebraicSpace.finiteSurjectiveAffineDescent S _ _
      ((Langlands.AlgebraicGeometry.AlgebraicSpace.schemeToSpace S).map f) hfin hsurj
      (Langlands.AlgebraicGeometry.AlgebraicSpace.schemeToSpace_isRepresentedByAffineScheme V)
  let e' : W ≅ U := (ULiftYoneda.fullyFaithful.{u + 1} (Over S)).preimageIso e
  have : IsAffine ((Over.forget S).obj W) := hW
  exact IsAffine.of_isIso ((Over.forget S).mapIso e').inv

/-- A scheme over `S` is affine once its reduced closed subscheme is affine. -/
theorem isAffine_of_isAffine_red {S : Scheme.{u}} (X : Over S)
    [IsAffine (ReducedSubgroup.red X.left)] : IsAffine X.left := by
  let V : Over S := Over.mk (ReducedSubgroup.redι X.left ≫ X.hom)
  have : IsAffine V.left := inferInstanceAs (IsAffine (ReducedSubgroup.red X.left))
  exact isAffine_of_finite_surjective (V := V) (Over.homMk (ReducedSubgroup.redι X.left) rfl)
    (inferInstanceAs (IsFinite (ReducedSubgroup.redι X.left)))
    ⟨ReducedSubgroup.redι_surjective X.left⟩

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **Algebraically closed case.** Over an algebraically closed field, a surjective
homomorphism from an affine group of finite type to a separated group of finite type has affine
target, given exact-kernel representations of normal closed subgroups of smooth groups. -/
theorem isAffineHom_of_isAlgClosed (hN : SmoothNormalKernelInput.{u})
    (G Q : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    [LocallyOfFiniteType Q.X.hom] [IsSeparated Q.X.hom]
    (q : G ⟶ Q) [Surjective q.hom.hom.left] :
    IsAffineHom Q.X.hom := by
  let q' : reducedSubgroup G ⟶ reducedSubgroup Q :=
    ReducedSubgroup.liftHom (reducedSubgroupι G ≫ q)
  have hfac : q'.hom.hom.left ≫ ReducedSubgroup.redι Q.X.left =
      ReducedSubgroup.redι G.X.left ≫ q.hom.hom.left :=
    ReducedSubgroup.redLift_fac _
  have : Surjective q'.hom.hom.left := by
    refine ⟨fun y => ?_⟩
    obtain ⟨w, hw⟩ := q.hom.hom.left.surjective (ReducedSubgroup.redι Q.X.left y)
    obtain ⟨x, rfl⟩ := ReducedSubgroup.redι_surjective G.X.left w
    refine ⟨x, ReducedSubgroup.redι_injective Q.X.left ?_⟩
    rw [← Scheme.Hom.comp_apply, hfac, Scheme.Hom.comp_apply, hw]
  have : IsSeparated (reducedSubgroup Q).X.hom :=
    inferInstanceAs (IsSeparated (ReducedSubgroup.redι Q.X.left ≫ Q.X.hom))
  obtain ⟨_, _, _⟩ := dominantGroupHomFlat k (reducedSubgroup G) (reducedSubgroup Q) q'
  have : IsAffineHom (reducedSubgroup Q).X.hom :=
    isAffineHom_of_smooth hN (reducedSubgroup G) (reducedSubgroup Q) q'
  have : IsAffine (ReducedSubgroup.red Q.X.left) :=
    isAffine_of_isAffineHom (reducedSubgroup Q).X.hom
  have : IsAffine Q.X.left := isAffine_of_isAffine_red Q.X
  infer_instance

end Reduced

/-- **Reduction.** Exact-kernel representations of normal closed subgroups of smooth affine
groups over algebraically closed fields imply the affine quotient theorem over every field. -/
theorem affineGroupSchemeQuotient_of_smoothNormalKernel (hN : SmoothNormalKernelInput.{u}) :
    AffineGroupSchemeQuotientStatement.{u} := by
  intro k _ G Q _ _ _ _ _ q _ _ _
  let b := toAlgebraicClosure k
  have : LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : LocallyOfFiniteType ((GroupScheme.baseChange b).obj Q).X.hom := by
    change LocallyOfFiniteType (pullback.snd Q.X.hom b)
    infer_instance
  have : IsSeparated ((GroupScheme.baseChange b).obj Q).X.hom := by
    change IsSeparated (pullback.snd Q.X.hom b)
    infer_instance
  have hp := DominantHomFlat.baseChange_isPullback b q
  have : Surjective ((GroupScheme.baseChange b).map q).hom.hom.left :=
    MorphismProperty.of_isPullback hp.flip ‹Surjective q.hom.hom.left›
  have : IsAffineHom ((GroupScheme.baseChange b).obj Q).X.hom :=
    isAffineHom_of_isAlgClosed hN _ _ ((GroupScheme.baseChange b).map q)
  have : IsAffine ((GroupScheme.baseChange b).obj Q).X.left :=
    isAffine_of_isAffineHom ((GroupScheme.baseChange b).obj Q).X.hom
  have : IsAffine Q.X.left :=
    Langlands.AlgebraicGeometry.fieldExtensionAffineDescent k (AlgebraicClosure k) Q.X.left
      Q.X.hom this
  infer_instance

end Langlands.GroupScheme.AffineQuotient
