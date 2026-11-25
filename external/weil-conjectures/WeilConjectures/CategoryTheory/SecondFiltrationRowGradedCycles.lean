/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries
import all WeilConjectures.CategoryTheory.DoubleComplexTotal

/-! # Row cycles in the second graded filtration

Source: Stacks Project, Homology, Tags 0130 and 012K.
(blueprint: lem-sp-second-filtration-row-graded-cycles).
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false

variable {C : Type uB} [Category.{vB} C] [Abelian C]

/-- Transfer the finite-summand quotient to evaluation of the quotient complex. -/
private theorem graded_term_iso
    (J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [J.HasTotal (ComplexShape.up ℤ)]
    (L : DecreasingFiltration (J.total (ComplexShape.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n = (J.secondFiltration n).step p)
    (p n : ℤ) (hpn : p ≤ n) :
    ∃ a : (J.X (n - p)).X p ⟶ (L.step p : CochainComplex C ℤ).X n,
      a ≫ (L.step p).arrow.f n =
        J.ιTotalOrZero (ComplexShape.up ℤ) (n - p) p n ∧
      IsIso (a ≫ (L.complexQuotientπ p (p + 1) (by omega)).f n) := by
  classical
  let S := (J.secondFiltration n).step p
  let T := (J.secondFiltration n).step (p + 1)
  let m := fun k : ℤ ↦ (L.step k).arrow.f n
  have hm : ∀ k, Mono (m k) := by
    intro k
    change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map (L.step k).arrow)
    infer_instance
  have he : ∀ k, (J.secondFiltration n).step k = Subobject.mk (m k) := by
    intro k
    rw [← hL, DecreasingFiltration.complexStep, imageSubobject_mono]
  let e := fun k ↦ Subobject.isoOfEqMk ((J.secondFiltration n).step k) (m k) (he k)
  have he_m : ∀ k, (e k).hom ≫ m k = ((J.secondFiltration n).step k).arrow := by
    intro k
    exact Subobject.ofLEMk_comp (he k).le
  let inc := Subobject.ofLE T S ((J.secondFiltration n).antitone_step (by omega))
  let l := Subobject.ofLE (L.step (p + 1)) (L.step p) (L.antitone_step (by omega))
  have hw : inc ≫ (e p).hom = (e (p + 1)).hom ≫ l.f n := by
    apply (cancel_mono (m p)).1
    rw [Category.assoc, he_m, Subobject.ofLE_arrow, Category.assoc]
    have hl : l.f n ≫ m p = m (p + 1) :=
      congrArg (fun f ↦ f.f n) (Subobject.ofLE_arrow
        (L.antitone_step (show p ≤ p + 1 by omega)))
    rw [hl, he_m]
  let proj : (J.total (ComplexShape.up ℤ)).X n ⟶ (J.X (n - p)).X p :=
    J.totalDesc (fun i j hij ↦ if hj : j = p then
      (J.XXIsoOfEq _ _ _ (by change i + j = n at hij; omega) hj).hom else 0)
  obtain ⟨b, hb, hbi⟩ := HomologicalComplex₂.finite_sup_cokernel_iso
    (fun i ↦ J.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n) p n proj
    (by
      rw [J.ιTotalOrZero_eq (ComplexShape.up ℤ) (n - p) p n (by
        change (n - p) + p = n; omega)]
      simp [proj, HomologicalComplex₂.XXIsoOfEq_rfl])
    (by
      intro i hi
      rw [J.ιTotalOrZero_eq (ComplexShape.up ℤ) (n - i) i n (by
        change (n - i) + i = n; omega)]
      simp [proj, hi])
    (by intro h; omega)
  change b ≫ S.arrow = _ at hb
  change IsIso (b ≫ cokernel.π inc) at hbi
  let ev := HomologicalComplex.eval C (ComplexShape.up ℤ) n
  let ec := cokernel.mapIso inc (ev.map l) (e (p + 1)) (e p) hw
  let eq := PreservesCokernel.iso ev l
  have hq : cokernel.π (ev.map l) ≫ eq.inv = (L.complexQuotientπ p (p + 1) (by omega)).f n := by
    apply (cancel_mono eq.hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (PreservesCokernel.π_iso_hom ev l).symm
  have hc : cokernel.π inc ≫ ec.hom ≫ eq.inv =
      (e p).hom ≫ (L.complexQuotientπ p (p + 1) (by omega)).f n := by
    have hec : cokernel.π inc ≫ ec.hom =
        (e p).hom ≫ cokernel.π (ev.map l) := cokernel.π_desc _ _ _
    rw [← Category.assoc, hec, Category.assoc, hq]
  refine ⟨b ≫ (e p).hom, ?_, ?_⟩
  · rw [Category.assoc, he_m, hb]
  · rw [Category.assoc, ← hc, ← Category.assoc]
    infer_instance

/-- Lift a diagonal inclusion through a step containing its image. -/
private theorem inclusion_lift
    (J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [J.HasTotal (ComplexShape.up ℤ)]
    (L : DecreasingFiltration (J.total (ComplexShape.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n = (J.secondFiltration n).step p)
    (p i j n : ℤ) (hij : i + j = n) (hpj : p ≤ j) (hjn : j ≤ n) :
    ∃ b : (J.X i).X j ⟶ (L.step p : CochainComplex C ℤ).X n,
      b ≫ (L.step p).arrow.f n = J.ιTotal (ComplexShape.up ℤ) i j n hij := by
  have hm : Mono ((L.step p).arrow.f n) := by
    change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map (L.step p).arrow)
    infer_instance
  have hle : imageSubobject (J.ιTotal (ComplexShape.up ℤ) i j n hij) ≤
      Subobject.mk ((L.step p).arrow.f n) := by
    rw [← imageSubobject_mono, ← DecreasingFiltration.complexStep, hL]
    have h := Finset.le_sup (f := fun k ↦ imageSubobject
      (J.ιTotalOrZero (ComplexShape.up ℤ) (n - k) k n))
      (Finset.mem_Icc.mpr ⟨hpj, hjn⟩)
    have hi : n - j = i := by omega
    rw [hi, J.ιTotalOrZero_eq (ComplexShape.up ℤ) i j n hij] at h
    exact h
  refine ⟨factorThruImageSubobject _ ≫ Subobject.ofLEMk _ _ hle, ?_⟩
  rw [Category.assoc, Subobject.ofLEMk_comp, imageSubobject_arrow_comp]

/-- The diagonal inclusions give graded term isomorphisms commuting with the row differential.
Source: Stacks Project, Tag 0130, clause 2.
(blueprint: lem-sp-second-filtration-row-graded-cycles).

Proof. Set J = flip(mappedFunctor F(I)). In degree n = s+r the filtration step
is the finite sum of images of the inclusions with second coordinate in [s,n].
Project the total coproduct onto the (r,s) summand and compose with the extension
isomorphism. This projection kills every summand with second coordinate greater
than s, hence kills the next step. Lift the (r,s) inclusion through the step.
The induced map into the quotient and the descended projection are inverse:
on the s summand their composite is identity, while all other summands belong
to the next step and vanish in the quotient. Evaluation preserves cokernels,
so this is the quotient of the subcomplexes used by L. Its normalization is
fixed uniquely by the monic step inclusion. On a diagonal inclusion the total
differential is the resolution differential plus the signed differential
raising s. The latter factors through step s+1 and is killed by its cokernel
projection. Extension by zero intertwines the resolution differentials with
their extensions. Cancel the monic step inclusion and then project to the
quotient to obtain the asserted square. The interval [s,s+r] contains s even
when s<0 or r=0. For a zero row the same projections and lifts give the
unique zero-object isomorphisms; no nonzero-object hypothesis is needed.
-/
private theorem secondFiltration_row_graded_terms
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    (F : A ⥤ B) [F.Additive]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (L : DecreasingFiltration
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
        (ComplexShape.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n =
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).secondFiltration n).step
        p)
    (s : ℤ) :
    ∃ a : ∀ r : ℕ,
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).X r ⟶
          (L.step s : CochainComplex B ℤ).X (s + (r : ℤ)),
      (∀ r, a r ≫ (L.step s).arrow.f (s + (r : ℤ)) =
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).extendXIso
          ComplexShape.embeddingUpNat (by rfl)).inv ≫
          (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).ιTotal
            (ComplexShape.up ℤ) (r : ℤ) s (s + (r : ℤ)) (by
              change (r : ℤ) + s = s + (r : ℤ)
              omega)) ∧
      (∀ r, IsIso (a r ≫
        (L.complexQuotientπ s (s + 1) (by omega)).f (s + (r : ℤ)))) ∧
      (∀ r,
        (a r ≫ (L.complexQuotientπ s (s + 1) (by omega)).f (s + (r : ℤ))) ≫
          (L.gradedPiece s).d (s + (r : ℤ)) (s + ((r + 1 : ℕ) : ℤ)) =
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).d r (r + 1) ≫
          (a (r + 1) ≫
            (L.complexQuotientπ s (s + 1) (by omega)).f
              (s + ((r + 1 : ℕ) : ℤ)))) := by
  classical
  let J := ((CartanEilenbergPresentation.mappedFunctor F).obj I).flip
  let R := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)
  have hterms : ∀ r : ℕ, ∃ a : R.X r ⟶
      (L.step s : CochainComplex B ℤ).X (s + (r : ℤ)),
      a ≫ (L.step s).arrow.f (s + (r : ℤ)) =
        (R.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv ≫
          J.ιTotal (ComplexShape.up ℤ) (r : ℤ) s (s + (r : ℤ)) (by
            change (r : ℤ) + s = s + (r : ℤ); omega) ∧
      IsIso (a ≫ (L.complexQuotientπ s (s + 1) (by omega)).f (s + (r : ℤ))) := by
    intro r
    have H := graded_term_iso J L hL s (s + (r : ℤ)) (by omega)
    have hn : s + (r : ℤ) - s = (r : ℤ) := by omega
    rw [hn] at H
    obtain ⟨b, hb, hbi⟩ := H
    let e : (J.X (r : ℤ)).X s ≅ R.X r :=
      R.extendXIso ComplexShape.embeddingUpNat (by rfl)
    refine ⟨e.inv ≫ b, ?_, ?_⟩
    · rw [Category.assoc, hb, J.ιTotalOrZero_eq (ComplexShape.up ℤ) (r : ℤ) s
        (s + (r : ℤ)) (by change (r : ℤ) + s = s + (r : ℤ); omega)]
    · rw [Category.assoc]
      infer_instance
  choose a ha hai using hterms
  refine ⟨a, ha, hai, ?_⟩
  intro r
  let n := s + (r : ℤ)
  let n' := s + ((r + 1 : ℕ) : ℤ)
  let q : (L.step s : CochainComplex B ℤ) ⟶ L.gradedPiece s :=
    L.complexQuotientπ s (s + 1) (by omega)
  let inc := Subobject.ofLE (L.step (s + 1)) (L.step s) (L.antitone_step (by omega))
  let e : (J.X (r : ℤ)).X s ≅ R.X r :=
    R.extendXIso ComplexShape.embeddingUpNat (by rfl)
  let e' : (J.X ((r + 1 : ℕ) : ℤ)).X s ≅ R.X (r + 1) :=
    R.extendXIso ComplexShape.embeddingUpNat (by rfl)
  obtain ⟨b, hb⟩ := inclusion_lift J L hL (s + 1) (r : ℤ) (s + 1) n'
    (by dsimp [n']; change (r : ℤ) + (s + 1) = s + ((r + 1 : ℕ) : ℤ); omega)
    le_rfl (by dsimp [n']; omega)
  have hm : Mono ((L.step s).arrow.f n') := by
    change Mono ((HomologicalComplex.eval B (ComplexShape.up ℤ) n').map (L.step s).arrow)
    infer_instance
  have heq : a r ≫ (L.step s : CochainComplex B ℤ).d n n' =
      R.d r (r + 1) ≫ a (r + 1) +
        (e.inv ≫ ((r : ℤ).negOnePow • (J.X (r : ℤ)).d s (s + 1))) ≫
          b ≫ inc.f n' := by
    apply (cancel_mono ((L.step s).arrow.f n')).1
    have hinc : inc.f n' ≫ (L.step s).arrow.f n' = (L.step (s + 1)).arrow.f n' :=
      congrArg (fun f ↦ f.f n')
        (Subobject.ofLE_arrow (L.antitone_step (show s ≤ s + 1 by omega)))
    simp only [Preadditive.add_comp, Category.assoc, hinc, hb]
    rw [← (L.step s).arrow.comm, ← Category.assoc, ha r, Category.assoc,
      J.total_d, Preadditive.comp_add, Preadditive.comp_add, J.ι_D₁, J.ι_D₂]
    rw [J.d₁_eq' (ComplexShape.up ℤ) (show
        (ComplexShape.up ℤ).Rel (r : ℤ) ((r + 1 : ℕ) : ℤ) by
          change (r : ℤ) + 1 = ((r + 1 : ℕ) : ℤ); omega),
      J.d₂_eq' (ComplexShape.up ℤ) (r : ℤ) (show
        (ComplexShape.up ℤ).Rel s (s + 1) by rfl)]
    change e.inv ≫ ((1 : ℤˣ) • _ ≫ _) +
      e.inv ≫ ((r : ℤ).negOnePow • _ ≫ _) = _
    rw [one_smul]
    have hD : (J.d (r : ℤ) ((r + 1 : ℕ) : ℤ)).f s =
        e.hom ≫ R.d r (r + 1) ≫ e'.inv :=
      R.extend_d_eq ComplexShape.embeddingUpNat (by rfl) (by rfl)
    rw [hD]
    have ha' : a (r + 1) ≫ (L.step s).arrow.f n' =
        e'.inv ≫ J.ιTotal (ComplexShape.up ℤ) ((r + 1 : ℕ) : ℤ) s n' (by
          change ((r + 1 : ℕ) : ℤ) + s = n'; dsimp [n']; omega) := ha (r + 1)
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [ha', J.ιTotalOrZero_eq (ComplexShape.up ℤ) ((r + 1 : ℕ) : ℤ) s n'
      (by change ((r + 1 : ℕ) : ℤ) + s = n'; dsimp [n']; omega),
      J.ιTotalOrZero_eq (ComplexShape.up ℤ) (r : ℤ) (s + 1) n'
        (by change (r : ℤ) + (s + 1) = n'; dsimp [n']; omega)]
    simp only [CategoryTheory.Linear.units_smul_comp]
  change (a r ≫ q.f n) ≫ (L.gradedPiece s).d n n' =
    R.d r (r + 1) ≫ (a (r + 1) ≫ q.f n')
  rw [Category.assoc, q.comm, ← Category.assoc, heq, Preadditive.add_comp]
  have hzero : inc.f n' ≫ q.f n' = 0 :=
    congrArg (fun f ↦ f.f n') (cokernel.condition inc)
  simp only [Category.assoc, hzero, comp_zero, add_zero]


/-- The normalized diagonal map induces an isomorphism on cycles, before taking
any quotient by boundaries.
Source: Stacks Project, Tag 0130, clause 2; Tag 012K, first-page cycle formula.
(blueprint: lem-sp-second-filtration-row-graded-cycles).

Proof. Write J = flip(mappedFunctor F(I)) and n = s+r. In degree n the second
step is the finite sum of the images of the diagonal inclusions with second
coordinate in [s,n]. Project the total coproduct onto its (r,s) summand, then
apply the extension isomorphism to recover the mapped row term. This projection
kills every summand of the next step, whose second coordinate is at least s+1.
It therefore descends to the graded quotient. Conversely lift the (r,s) summand
through the step and project to the quotient. On all generating inclusions these
two morphisms are inverse: the summand s gives identity, and all other summands
are killed in the quotient. This proves the degreewise graded comparison.
The total differential of the diagonal inclusion is the resolution differential
plus the signed differential raising s. The latter factors through the next
step and disappears in the quotient. Thus the comparison intertwines the row
differential with the graded differential. Apply the universal property of the
kernels of these outgoing differentials to obtain a mutually inverse pair of
cycle maps. The first-page cycle formula identifies the graded kernel with
L.complexCycles s n 1. Monicity of the filtration inclusion forces the given t
to equal the restriction of the term lift, so the asserted normalization follows.
This uses [s,n], never s>=0. At r=0 the interval contains just s; no incoming
term or boundary calculation is used. Zero rows give the unique zero-object iso.
-/
theorem secondFiltration_row_graded_cycles
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    (F : A ⥤ B) [F.Additive]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (L : DecreasingFiltration
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
        (ComplexShape.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n =
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).secondFiltration n).step
        p)
    (r : ℕ) (s : ℤ)
    (t : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).cycles r ⟶
      (L.step s : CochainComplex B ℤ).X (s + (r : ℤ)))
    (ht : t ≫ (L.step s).arrow.f (s + (r : ℤ)) =
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).iCycles r ≫
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).extendXIso
        ComplexShape.embeddingUpNat (by rfl)).inv ≫
        (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).ιTotal
          (ComplexShape.up ℤ) (r : ℤ) s (s + (r : ℤ)) (by
            change (r : ℤ) + s = s + (r : ℤ)
            omega))) :
    ∃ c : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).cycles r ≅
        (L.complexCycles s (s + (r : ℤ)) 1 : B),
      c.hom ≫ (L.complexCycles s (s + (r : ℤ)) 1).arrow =
        t ≫ (L.complexQuotientπ s (s + 1) (by omega)).f (s + (r : ℤ)) := by
  obtain ⟨a, ha, hai, hd⟩ := secondFiltration_row_graded_terms F I L hL s
  let R := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)
  let n := s + (r : ℤ)
  let n' := s + ((r + 1 : ℕ) : ℤ)
  let q : (L.step s : CochainComplex B ℤ) ⟶ L.gradedPiece s :=
    L.complexQuotientπ s (s + 1) (by omega)
  have ht' : t = R.iCycles r ≫ a r := by
    have : Mono ((L.step s).arrow.f n) := by
      change Mono ((HomologicalComplex.eval B (ComplexShape.up ℤ) n).map
        (L.step s).arrow)
      infer_instance
    apply (cancel_mono ((L.step s).arrow.f n)).1
    change t ≫ (L.step s).arrow.f (s + (r : ℤ)) = _
    rw [Category.assoc, ha]
    exact ht
  have hZ := (L.filteredComplex_firstPage_cycles_boundaries s n).1
  have hn : n + 1 = n' := by dsimp [n, n']; omega
  rw [hn] at hZ
  have hr : (ComplexShape.up ℕ).next r = r + 1 := by
    apply ComplexShape.next_eq'
    rfl
  have := hai r
  have := hai (r + 1)
  let e : R.X r ≅ (L.gradedPiece s).X n := asIso (a r ≫ q.f n)
  let e' : R.X (r + 1) ≅ (L.gradedPiece s).X n' :=
    asIso (a (r + 1) ≫ q.f n')
  let k :=
    (R.cyclesIsKernel r (r + 1) hr).conePointUniqueUpToIso
      (kernelIsKernel (R.d r (r + 1)))
  let c := k ≪≫ Limits.kernel.mapIso (R.d r (r + 1))
    ((L.gradedPiece s).d n n') e e' (hd r).symm ≪≫
    (kernelSubobjectIso ((L.gradedPiece s).d n n')).symm ≪≫
    Subobject.isoOfEq _ _ hZ.symm
  refine ⟨c, ?_⟩
  change c.hom ≫ (L.complexCycles s n 1).arrow = t ≫ q.f n
  dsimp only [c, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Subobject.isoOfEq_hom, Subobject.ofLE_arrow,
    kernelSubobject_arrow', Limits.kernel.mapIso_hom, Limits.kernel.map, Limits.kernel.lift_ι]
  rw [← Category.assoc]
  have hk : k.hom ≫ Limits.kernel.ι (R.d r (r + 1)) = R.iCycles r :=
    (R.cyclesIsKernel r (r + 1) hr).conePointUniqueUpToIso_hom_comp
      (kernelIsKernel (R.d r (r + 1))) WalkingParallelPair.zero
  rw [hk, ht']
  exact (Category.assoc _ _ _).symm

end CategoryTheory.Functor
