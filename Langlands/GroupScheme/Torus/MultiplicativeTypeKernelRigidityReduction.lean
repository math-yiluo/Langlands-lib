import Langlands.GroupScheme.Torus.MultiplicativeTypeKernelFibreModel
import Langlands.GroupScheme.Torus.MultiplicativeTypeKernelNeighborhood
import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralRigidityStatement
import Langlands.GroupScheme.KernelSquareTransport
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Relative multiplicative-type kernels from rigidity and monomorphism spreading -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.MultiplicativeTypeKernelReduction

section Transport

variable {S : Scheme.{u}} {H G N H' G' N' : GroupScheme S}

/-- A compatible isomorphism of the ambient arrow and subgroup preserves
equality with its full scheme-theoretic kernel range. -/
theorem kernel_range_eq_of_iso
    (f : H ⟶ G) (i : N ⟶ H) [Mono i.hom.hom]
    (f' : H' ⟶ G') (i' : N' ⟶ H')
    (eH : H ≅ H') (eG : G ≅ G') (eN : N ≅ N')
    (hf : eH.hom ≫ f' = f ≫ eG.hom)
    (hi : eN.hom ≫ i' = i ≫ eH.hom)
    (hker : SubgroupFunctor.range (kernelι f) = SubgroupFunctor.range i) :
    SubgroupFunctor.range (kernelι f') = SubgroupFunctor.range i' := by
  let k := KernelRepresentative.iso f i hker
  let K := kernelSquareIso f f' eH eG hf
  let e : N' ≅ kernel f' := eN.symm ≪≫ k.symm ≪≫ K
  have hk : k.inv ≫ kernelι f = i := by
    calc
      _ = k.inv ≫ (k.hom ≫ i) :=
        congrArg (fun t => k.inv ≫ t) (KernelRepresentative.iso_hom_comp f i hker).symm
      _ = _ := by rw [Iso.inv_hom_id_assoc]
  have he : e.hom ≫ kernelι f' = i' := by
    dsimp only [e, K, Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc, kernelSquareIso_hom_ι]
    rw [← Category.assoc k.inv, hk, ← hi, Iso.inv_hom_id_assoc]
  have hr := SubgroupFunctor.range_iso_comp e (kernelι f')
  rw [he] at hr
  exact hr.symm

variable {T U : Scheme.{u}}

/-- The actual kernel comparison for iterated change of base. -/
def kernelBaseChangeCompIso (b : T ⟶ S) (a : U ⟶ T) (f : H ⟶ G) :
    kernel ((baseChange (a ≫ b)).map f) ≅
      kernel ((baseChange a).map ((baseChange b).map f)) :=
  kernelSquareIso _ _ (baseChangeCompIso b a H) (baseChangeCompIso b a G)
    (((Functor.mapGrpNatIso (Over.pullbackComp a b)) ≪≫
      Functor.mapGrpCompIso).hom.naturality f).symm

/-- Full-kernel range equality commutes with the comparison between
iterated base change and base change along the composite. -/
theorem kernel_range_eq_iterated_iff (b : T ⟶ S) (a : U ⟶ T)
    (f : H ⟶ G) (i : N ⟶ H) [Mono i.hom.hom] :
    (SubgroupFunctor.range (kernelι ((baseChange a).map ((baseChange b).map f))) =
        SubgroupFunctor.range ((baseChange a).map ((baseChange b).map i))) ↔
      SubgroupFunctor.range (kernelι ((baseChange (a ≫ b)).map f)) =
        SubgroupFunctor.range ((baseChange (a ≫ b)).map i) := by
  let eH := baseChangeCompIso b a H
  let eG := baseChangeCompIso b a G
  let eN := baseChangeCompIso b a N
  have hf : eH.hom ≫ (baseChange a).map ((baseChange b).map f) =
      (baseChange (a ≫ b)).map f ≫ eG.hom :=
    (((Functor.mapGrpNatIso (Over.pullbackComp a b)) ≪≫
      Functor.mapGrpCompIso).hom.naturality f).symm
  have hi : eN.hom ≫ (baseChange a).map ((baseChange b).map i) =
      (baseChange (a ≫ b)).map i ≫ eH.hom :=
    (((Functor.mapGrpNatIso (Over.pullbackComp a b)) ≪≫
      Functor.mapGrpCompIso).hom.naturality i).symm
  have : Mono ((baseChange b).map i).hom.hom := by
    change Mono ((Over.pullback b).map i.hom.hom)
    infer_instance
  have : Mono ((baseChange a).map ((baseChange b).map i)).hom.hom := by
    change Mono ((Over.pullback a).map ((baseChange b).map i).hom.hom)
    infer_instance
  have : Mono ((baseChange (a ≫ b)).map i).hom.hom := by
    change Mono ((Over.pullback (a ≫ b)).map i.hom.hom)
    infer_instance
  constructor
  · intro h
    apply kernel_range_eq_of_iso
      ((baseChange a).map ((baseChange b).map f))
      ((baseChange a).map ((baseChange b).map i))
      ((baseChange (a ≫ b)).map f) ((baseChange (a ≫ b)).map i)
      eH.symm eG.symm eN.symm _ _ h
    · apply (cancel_mono eG.hom).mp
      simp only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id]
      rw [← hf, Iso.inv_hom_id_assoc]
    · apply (cancel_mono eH.hom).mp
      simp only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id]
      rw [← hi, Iso.inv_hom_id_assoc]
  · intro h
    exact kernel_range_eq_of_iso
      ((baseChange (a ≫ b)).map f) ((baseChange (a ≫ b)).map i)
      ((baseChange a).map ((baseChange b).map f))
      ((baseChange a).map ((baseChange b).map i))
      eH eG eN hf hi h

/-- A full-kernel range equation at a point remains the same equation at
the corresponding point of an open subscheme. -/
theorem kernel_range_eq_restrict_residue (W : S.Opens) (s : W)
    (f : H ⟶ G) (i : N ⟶ H) [Mono i.hom.hom]
    (hs :
      SubgroupFunctor.range
          (kernelι ((baseChange (S.fromSpecResidueField (W.ι s))).map f)) =
        SubgroupFunctor.range ((baseChange (S.fromSpecResidueField (W.ι s))).map i)) :
    SubgroupFunctor.range
        (kernelι ((baseChange (W.toScheme.fromSpecResidueField s)).map ((baseChange W.ι).map f))) =
      SubgroupFunctor.range
        ((baseChange (W.toScheme.fromSpecResidueField s)).map ((baseChange W.ι).map i)) := by
  let c := S.fromSpecResidueField (W.ι s)
  let d := Spec.map (W.ι.residueFieldMap s)
  have h0 :
      SubgroupFunctor.range (kernelι ((baseChange d).map ((baseChange c).map f))) =
        SubgroupFunctor.range ((baseChange d).map ((baseChange c).map i)) := by
    rw [kernel_range_baseChange, SubgroupFunctor.range_baseChangeHom, hs]
  apply (kernel_range_eq_iterated_iff W.ι (W.toScheme.fromSpecResidueField s) f i).2
  have hc := (kernel_range_eq_iterated_iff c d f i).1 h0
  have hd : d ≫ c = W.toScheme.fromSpecResidueField s ≫ W.ι :=
    W.ι.SpecMap_residueFieldMap_fromSpecResidueField s
  rwa [hd] at hc

end Transport

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- An actual open cover on which the full kernels have multiplicative type. -/
structure KernelOpenCover (f : H ⟶ G) where
  cover : S.OpenCover
  multiplicativeType : ∀ i, RelativeMultiplicativeType.IsMultiplicativeType
    (kernel ((baseChange (cover.f i)).map f))

namespace KernelOpenCover

/-- Multiplicative type of the actual kernels on the open cover descends
to multiplicative type of the original full kernel. -/
theorem isMultiplicativeType_kernel {f : H ⟶ G} (C : KernelOpenCover f) :
    RelativeMultiplicativeType.IsMultiplicativeType (kernel f) := by
  let D : Scheme.Cover Scheme.fppfPrecoverage S :=
    C.cover.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun _ => ⟨inferInstance, inferInstance⟩)
  apply RelativeMultiplicativeType.IsMultiplicativeType.of_fppfCover D
  intro i
  exact RelativeMultiplicativeType.IsMultiplicativeType.of_iso
    (kernelBaseChangeIso (C.cover.f i) f) (C.multiplicativeType i)

end KernelOpenCover

section Split

open RelativeMultiplicativeType

variable
    (h5 : MultiplicativeTypeCentralRigidityStatement.{u})
    (h6 : MultiplicativeTypeMonomorphismSpreadingStatement.{u})
    {S : Scheme.{u}} {M : Type u} [AddCommGroup M] [AddGroup.FG M]
    {G : GroupScheme S} [IsSeparated G.X.hom]
    (f : diagonalizable S M ⟶ G)
    (hfin : IsLocallyNoetherian S ∨
      (LocallyOfFinitePresentation G.X.hom ∧ QuasiCompact G.X.hom ∧
        QuasiSeparated G.X.hom))

include h5 h6 hfin

/-- The split-source kernel is multiplicative type on an open neighborhood
of every base point, conditional on the two exact rigidity and spreading inputs. -/
theorem exists_split_neighborhood (s : S) :
    ∃ (T : Scheme.{u}) (b : T ⟶ S),
      IsOpenImmersion b ∧ s ∈ Set.range b ∧
        RelativeMultiplicativeType.IsMultiplicativeType (kernel ((baseChange b).map f)) := by
  let c := S.fromSpecResidueField s
  let m := fibreClosedSubgroupModel f c
  let i := fibreSubgroupHom f c
  let q := diagonalizableExactQuotientMap S m.restriction
  have hN : RelativeMultiplicativeType.IsMultiplicativeType (fibreSubgroup f c) :=
    RelativeMultiplicativeType.IsMultiplicativeType.of_isDiagonalizable
      (isDiagonalizable_fibreSubgroup f c)
  have hQ : RelativeMultiplicativeType.IsMultiplicativeType
      (diagonalizable S m.restriction.ker) :=
    isMultiplicativeType_diagonalizableExactQuotient S m.restriction
  have hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q :=
    isFppfQuotient_diagonalizableExactQuotientMap S m.restriction m.surjective
  have hqa : IsAffineHom q.hom.hom.left :=
    isAffineHom_diagonalizableExactQuotientMap S m.restriction
  have hic : IsClosedSubgroup i := isClosedSubgroup_fibreSubgroupHom f c
  have : IsClosedImmersion i.hom.hom.left := hic
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨W, hsW, hkill⟩ := (h5 S (fibreSubgroup f c) G hN hfin).2.1
    (i ≫ f) s (fibreSubgroupHom_comp_fibre_eq_one f c)
  let w : W := ⟨s, hsW⟩
  let B := baseChange W.ι
  let fW := B.map f
  let iW := B.map i
  let qW := B.map q
  have hqW : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range iW) qW := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hq.baseChange W.ι
  have : IsAffineHom qW.hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsAffineHom) W.ι q.hom.hom hqa
  have : Mono iW.hom.hom := by
    change Mono ((Over.pullback W.ι).map i.hom.hom)
    infer_instance
  have hkillW : (iW ≫ fW).hom.hom = 1 := by
    change (B.map i ≫ B.map f).hom.hom = 1
    rw [← B.map_comp]
    exact hkill
  have hGW : IsSeparated (B.obj G).X.hom := by
    change IsSeparated (CategoryTheory.Limits.pullback.snd _ _)
    infer_instance
  have hfinW : IsLocallyNoetherian W.toScheme ∨
      LocallyOfFinitePresentation (B.obj G).X.hom := by
    rcases hfin with hS | ⟨hfp, _, _⟩
    · have := hS
      exact Or.inl (isLocallyNoetherian_of_isOpenImmersion W.ι)
    · have := hfp
      refine Or.inr ?_
      change LocallyOfFinitePresentation (CategoryTheory.Limits.pullback.snd _ _)
      infer_instance
  have hkerW :
      SubgroupFunctor.range (kernelι
          ((baseChange (W.toScheme.fromSpecResidueField w)).map fW)) =
        SubgroupFunctor.range
          ((baseChange (W.toScheme.fromSpecResidueField w)).map iW) :=
    kernel_range_eq_restrict_residue W w f i (kernel_range_eq_fibreSubgroup f c)
  obtain ⟨U, hwU, _, hKU⟩ :=
    MultiplicativeTypeKernelNeighborhood.exists_neighborhood fW iW qW hqW hkillW
      h6 (hN.baseChange W.ι) (hQ.baseChange W.ι) hGW hfinW w hkerW
  refine ⟨U.toScheme, U.ι ≫ W.ι, inferInstance, ?_, ?_⟩
  · refine ⟨⟨w, hwU⟩, ?_⟩
    rw [Scheme.Hom.comp_apply]
    rfl
  · exact RelativeMultiplicativeType.IsMultiplicativeType.of_iso
      (kernelBaseChangeCompIso W.ι U.ι f) hKU

/-- Choose an actual open cover for the split-source kernel, conditional
on the two exact rigidity and spreading theorems. -/
def splitKernelOpenCover : KernelOpenCover f := by
  classical
  choose T b hb hs hk using fun s : S => exists_split_neighborhood h5 h6 f hfin s
  let C : S.OpenCover :=
    { I₀ := S
      X := T
      f := b
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun s => ⟨s, hs s⟩, fun s => hb s⟩ }
  exact ⟨C, hk⟩

/-- Rigidity and monomorphism spreading prove the complete kernel criterion
for a diagonalizable source over an arbitrary base scheme. -/
theorem isMultiplicativeType_kernel_split :
    RelativeMultiplicativeType.IsMultiplicativeType (kernel f) :=
  (splitKernelOpenCover h5 h6 f hfin).isMultiplicativeType_kernel

end Split

section General

variable
    (h5 : MultiplicativeTypeCentralRigidityStatement.{u})
    (h6 : MultiplicativeTypeMonomorphismSpreadingStatement.{u})

include h5 h6

/-- The exact general relative kernel criterion follows from the exact
central-rigidity and monomorphism-spreading statements, with no extra
geometric hypotheses. Both statements remain explicit premises. -/
theorem isMultiplicativeType_kernel
    {S : Scheme.{u}} {H G : GroupScheme S} (f : H ⟶ G)
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (hG : IsSeparated G.X.hom)
    (hfin : IsLocallyNoetherian S ∨
      (LocallyOfFinitePresentation G.X.hom ∧ QuasiCompact G.X.hom ∧
        QuasiSeparated G.X.hom)) :
    RelativeMultiplicativeType.IsMultiplicativeType (kernel f) := by
  have : IsSeparated G.X.hom := hG
  obtain ⟨C, hC⟩ := hH
  let D : Scheme.Cover Scheme.fppfPrecoverage S := C
  apply RelativeMultiplicativeType.IsMultiplicativeType.of_fppfCover D
  intro j
  apply RelativeMultiplicativeType.IsMultiplicativeType.of_iso
    (kernelBaseChangeIso (C.f j) f)
  obtain ⟨M, _, _, ⟨e⟩⟩ := hC j
  let B := baseChange (C.f j)
  let g := e.inv ≫ B.map f
  have : IsSeparated (B.obj G).X.hom := by
    change IsSeparated (CategoryTheory.Limits.pullback.snd _ _)
    infer_instance
  have hfin' : IsLocallyNoetherian (C.X j) ∨
      (LocallyOfFinitePresentation (B.obj G).X.hom ∧
        QuasiCompact (B.obj G).X.hom ∧ QuasiSeparated (B.obj G).X.hom) := by
    rcases hfin with hS | ⟨hfp, hqc, hqs⟩
    · have := hS
      have : LocallyOfFinitePresentation (C.f j) := (C.map_prop j).2
      exact Or.inl (LocallyOfFiniteType.isLocallyNoetherian (C.f j))
    · have := hfp
      have := hqc
      have := hqs
      refine Or.inr ⟨?_, ?_, ?_⟩
      · change LocallyOfFinitePresentation (CategoryTheory.Limits.pullback.snd _ _)
        infer_instance
      · change QuasiCompact (CategoryTheory.Limits.pullback.snd _ _)
        infer_instance
      · change QuasiSeparated (CategoryTheory.Limits.pullback.snd _ _)
        infer_instance
  exact RelativeMultiplicativeType.IsMultiplicativeType.of_iso
    (kernelCoordinateIso (B.map f) g e.symm rfl).symm
    (isMultiplicativeType_kernel_split h5 h6 g hfin')

end General

end Langlands.GroupScheme.MultiplicativeTypeKernelReduction
