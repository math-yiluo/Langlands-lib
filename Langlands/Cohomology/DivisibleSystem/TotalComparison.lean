import Langlands.Cohomology.DivisibleSystem.InvariantTotal
import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# The augmentation of the total complexes to the system itself

The Total module totalizes the augmentation of the standard resolutions. Its target is the total
complex, with rows `q < N`, of an `ℓ`-divisible system `K` of `ℕ`-graded cochain complexes placed
in resolution degree `0`. This module compares that target with `K` extended by zero to
`ℤ`-graded cochain complexes (Mathlib's `HomologicalComplex.extend` along
`ComplexShape.embeddingUpNat`). If every member of `K` vanishes in degrees `q ≥ N`, the
comparison is an isomorphism of `ℓ`-divisible systems; composing it with the totalized
augmentation gives a morphism from the total complexes to `K` extended to `ℤ` (Harris 1999, §2,
the augmentation `C_m^{•,H} → M_m^{•,H}` implicit in (2.5)). The hypothesis is discharged for
the truncated smooth Godement systems with `N = D + 2`.

No quasi-isomorphism and no freeness is proved, and no comparison between different subgroups.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits

universe w v u uR uG

section Extend

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- Extension of complexes along an embedding of complex shapes preserves finite limits:
in each degree it is either evaluation or the zero functor. -/
instance extendFunctor_preservesFiniteLimits {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} (e : c.Embedding c') : PreservesFiniteLimits (e.extendFunctor A) :=
  ⟨fun _ _ _ => HomologicalComplex.preservesLimitsOfShape_of_eval _ fun i' => by
    by_cases h : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := h
      exact preservesLimitsOfShape_of_natIso (e.extendFunctorCompEvalIso A hi).symm
    · exact Functor.preservesLimitsOfShape_of_isZero _
        ((Functor.isZero_iff _).2 fun K => K.isZero_extend_X e i' fun i hi => h ⟨i, hi⟩) _⟩

/-- Extension of complexes along an embedding of complex shapes preserves finite colimits. -/
instance extendFunctor_preservesFiniteColimits {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} (e : c.Embedding c') : PreservesFiniteColimits (e.extendFunctor A) :=
  ⟨fun _ _ _ => HomologicalComplex.preservesColimitsOfShape_of_eval _ fun i' => by
    by_cases h : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := h
      exact preservesColimitsOfShape_of_natIso (e.extendFunctorCompEvalIso A hi).symm
    · exact Functor.preservesColimitsOfShape_of_isZero _
        ((Functor.isZero_iff _).2 fun K => K.isZero_extend_X e i' fun i hi => h ⟨i, hi⟩) _⟩

end Extend

section Column

variable {A : Type u} [Category.{v} A] [Abelian A] (N : ℕ)

/-- A cochain complex placed in resolution degree `0`, as a double complex. -/
abbrev columnZero (A : Type u) [Category.{v} A] [Abelian A] :
    CochainComplex A ℕ ⥤ HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.down ℕ) :=
  (ChainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℕ)

/-- The total complex, rows `q < N`, of `L` placed in resolution degree `0`. -/
abbrev columnTotal (L : CochainComplex A ℕ) : CochainComplex A ℤ :=
  (upFinTotalFunctor A N).obj ((columnZero A).obj L)

/-- The rows `q < N` of `L` placed in resolution degree `0`; `columnTotal N L` is its total
complex. -/
abbrev columnRestriction (L : CochainComplex A ℕ) :
    HomologicalComplex₂ A (upFin N) (ComplexShape.down ℕ) :=
  ((upFinEmbedding N).restrictionFunctor _).obj ((columnZero A).obj L)

/-- `L` extended by zero to a `ℤ`-graded cochain complex. -/
abbrev extendInt (L : CochainComplex A ℕ) : CochainComplex A ℤ :=
  L.extend ComplexShape.embeddingUpNat

lemma isZero_columnZero_X_X_succ (L : CochainComplex A ℕ) (q r : ℕ) :
    IsZero ((((columnZero A).obj L).X q).X (r + 1)) :=
  HomologicalComplex.isZero_single_obj_X _ 0 _ (r + 1) (Nat.succ_ne_zero r)

/-- The component of the comparison on the summand `(q, r)` of total degree `n`: the
identification of the degree `q` term of `L` with the degree `n = q` term of its extension if
`r = 0`, and `0` otherwise (the summand is then zero). -/
def columnSummand (L : CochainComplex A ℕ) (n : ℤ) (q : Fin N) :
    (r : ℕ) → ((q : ℕ) : ℤ) - r = n →
      ((((columnZero A).obj L).X q).X r ⟶ (extendInt L).X n)
  | 0, h => (L.extendXIso ComplexShape.embeddingUpNat (by simpa using h)).inv
  | _ + 1, _ => 0

/-- Degree `n` of the comparison from the total complex of `L` in resolution degree `0` to the
extension of `L`. -/
def columnComparisonF (L : CochainComplex A ℕ) (n : ℤ) :
    ((columnRestriction N L).total (ComplexShape.up ℤ)).X n ⟶ (extendInt L).X n :=
  HomologicalComplex₂.totalDesc _ (fun q r h => columnSummand N L n q r h)

@[reassoc]
lemma ιTotal_columnComparisonF (L : CochainComplex A ℕ) (n : ℤ) (q : Fin N) (r : ℕ)
    (h : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) = n) :
    (columnRestriction N L).ιTotal (ComplexShape.up ℤ) q r n h ≫ columnComparisonF N L n =
      columnSummand N L n q r h :=
  HomologicalComplex₂.ι_totalDesc _ _ _ _ _

lemma columnSummand_zero (L : CochainComplex A ℕ) (n : ℤ) (q : Fin N)
    (h : ((q : ℕ) : ℤ) - (0 : ℕ) = n) :
    columnSummand N L n q 0 h =
      (L.extendXIso ComplexShape.embeddingUpNat (by simpa using h)).inv :=
  rfl

/-- The comparison commutes with the differentials when `L` vanishes in degree `N`. -/
lemma columnComparisonF_comm (L : CochainComplex A ℕ) (hL : IsZero (L.X N)) (n n' : ℤ)
    (hnn' : (ComplexShape.up ℤ).Rel n n') :
    columnComparisonF N L n ≫ (extendInt L).d n n' =
      ((columnRestriction N L).total (ComplexShape.up ℤ)).d n n' ≫
        columnComparisonF N L n' := by
  have hnn'' : n + 1 = n' := hnn'
  refine HomologicalComplex₂.total.hom_ext _ fun q r h => ?_
  cases r with
  | succ r => exact (isZero_columnZero_X_X_succ L q r).eq_of_src _ _
  | zero =>
    have hq : ((q : ℕ) : ℤ) = n := by
      have h' : ((q : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = n := h
      simpa using h'
    rw [ιTotal_columnComparisonF_assoc, columnSummand_zero,
      L.extend_d_eq ComplexShape.embeddingUpNat (i := (q : ℕ)) (j := (q : ℕ) + 1)
        (by simpa using hq) (by simp; omega)]
    refine (Iso.inv_hom_id_assoc _ _).trans ?_
    rw [HomologicalComplex₂.total_d, Preadditive.add_comp, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc,
      HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ (fun h0 => Nat.succ_ne_zero _ h0), zero_comp,
      add_zero]
    by_cases hqN : (q : ℕ) + 1 < N
    · have hrel : (upFin N).Rel q ⟨(q : ℕ) + 1, hqN⟩ := rfl
      have hπ : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ)
          (⟨(q : ℕ) + 1, hqN⟩, 0) = n' := by
        rw [upFin_π]
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
        omega
      rw [HomologicalComplex₂.d₁_eq _ _ hrel 0 n' hπ]
      have hε : ComplexShape.ε₁ (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, 0) = 1 :=
        rfl
      rw [hε, one_smul, Category.assoc, ιTotal_columnComparisonF, columnSummand_zero]
      exact congrArg (· ≫ _) (ChainComplex.single₀_map_f_zero (L.d (q : ℕ) ((q : ℕ) + 1))).symm
    · have hN : (q : ℕ) + 1 = N := by
        have := q.isLt
        omega
      have hd : L.d (q : ℕ) ((q : ℕ) + 1) = 0 := (hN ▸ hL).eq_of_tgt _ _
      have hnext : ¬ (upFin N).Rel q ((upFin N).next q) := fun hr => by
        have hr' : (q : ℕ) + 1 = ((upFin N).next q : ℕ) := hr
        have := ((upFin N).next q).isLt
        omega
      rw [hd, HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ hnext, zero_comp, zero_comp]
      rfl

/-- The comparison from the total complex, rows `q < N`, of `L` in resolution degree `0` to the
extension of `L`, for `L` vanishing in degrees `q ≥ N`. -/
def columnComparison (L : CochainComplex A ℕ) (hL : ∀ q, N ≤ q → IsZero (L.X q)) :
    columnTotal N L ⟶ extendInt L where
  f n := columnComparisonF N L n
  comm' n n' h := columnComparisonF_comm N L (hL N le_rfl) n n' h

lemma columnComparison_f (L : CochainComplex A ℕ) (hL : ∀ q, N ≤ q → IsZero (L.X q)) (n : ℤ) :
    (columnComparison N L hL).f n = columnComparisonF N L n :=
  rfl

/-- The comparison is natural in `L`. -/
lemma columnComparisonF_naturality {L L' : CochainComplex A ℕ} (f : L ⟶ L') (n : ℤ) :
    (HomologicalComplex₂.total.map (((upFinEmbedding N).restrictionFunctor _).map
        ((columnZero A).map f)) (ComplexShape.up ℤ)).f n ≫ columnComparisonF N L' n =
      columnComparisonF N L n ≫
        (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat).f n := by
  refine HomologicalComplex₂.total.hom_ext _ fun q r h => ?_
  cases r with
  | succ r => exact (isZero_columnZero_X_X_succ L q r).eq_of_src _ _
  | zero =>
    have hq : ((q : ℕ) : ℤ) = n := by
      have h' : ((q : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = n := h
      simpa using h'
    have hmap := HomologicalComplex₂.ιTotal_map _ _
      (((upFinEmbedding N).restrictionFunctor _).map ((columnZero A).map f))
      (ComplexShape.up ℤ) q 0 n h
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ columnComparisonF N L' n) hmap).trans ?_
    rw [Category.assoc, ιTotal_columnComparisonF, ιTotal_columnComparisonF_assoc,
      columnSummand_zero, columnSummand_zero,
      HomologicalComplex.extendMap_f f ComplexShape.embeddingUpNat (i := (q : ℕ))
        (by simpa using hq)]
    refine Eq.trans ?_ (Iso.inv_hom_id_assoc (L.extendXIso ComplexShape.embeddingUpNat
      (i := (q : ℕ)) (i' := n) (by simpa using hq)) _).symm
    exact congrArg (· ≫ _) (ChainComplex.single₀_map_f_zero (f.f (q : ℕ)))

/-- The total complex of `L` in resolution degree `0` is zero in negative degrees. -/
lemma isZero_columnTotal_X_of_neg (L : CochainComplex A ℕ) {n : ℤ} (hn : n < 0) :
    IsZero (((columnRestriction N L).total (ComplexShape.up ℤ)).X n) := by
  rw [IsZero.iff_id_eq_zero]
  refine HomologicalComplex₂.total.hom_ext _ fun q r h => ?_
  cases r with
  | succ r => exact (isZero_columnZero_X_X_succ L q r).eq_of_src _ _
  | zero =>
    have h' : ((q : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = n := h
    omega

lemma isIso_columnComparisonF (L : CochainComplex A ℕ) (hL : ∀ q, N ≤ q → IsZero (L.X q))
    (n : ℤ) : IsIso (columnComparisonF N L n) := by
  obtain hn | hn := lt_or_ge n 0
  · exact isIso_of_source_target_iso_zero _ (isZero_columnTotal_X_of_neg N L hn).isoZero
      (L.isZero_extend_X _ n (fun i hi => by simp at hi; omega)).isoZero
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  have he : ComplexShape.embeddingUpNat.f q = (q : ℤ) := rfl
  by_cases hqN : q < N
  · have hπ : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ)
        (⟨q, hqN⟩, 0) = (q : ℤ) := by
      rw [upFin_π]
      simp
    refine ⟨(L.extendXIso ComplexShape.embeddingUpNat he).hom ≫
      (columnRestriction N L).ιTotal (ComplexShape.up ℤ) ⟨q, hqN⟩ 0 (q : ℤ) hπ, ?_, ?_⟩
    · refine HomologicalComplex₂.total.hom_ext _ fun q' r h => ?_
      cases r with
      | succ r => exact (isZero_columnZero_X_X_succ L q' r).eq_of_src _ _
      | zero =>
        have h' : ((q' : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = q := h
        obtain rfl : q' = ⟨q, hqN⟩ := Fin.ext (by change (q' : ℕ) = q; omega)
        refine (ιTotal_columnComparisonF_assoc N L _ _ _ h _).trans ?_
        refine (Iso.inv_hom_id_assoc (L.extendXIso ComplexShape.embeddingUpNat he) _).trans ?_
        exact (Category.comp_id _).symm
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg ((L.extendXIso ComplexShape.embeddingUpNat he).hom ≫ ·)
        (ιTotal_columnComparisonF N L _ _ _ hπ)).trans ?_
      exact Iso.hom_inv_id _
  · exact isIso_of_source_target_iso_zero _
      (isZero_total_X A N _ (by omega)).isoZero
      ((hL q (by omega)).of_iso (L.extendXIso ComplexShape.embeddingUpNat he)).isoZero

instance isIso_columnComparison (L : CochainComplex A ℕ) (hL : ∀ q, N ≤ q → IsZero (L.X q)) :
    IsIso (columnComparison N L hL) :=
  @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ _ fun n =>
    isIso_columnComparisonF N L hL n

end Column

namespace DivisibleSystem

section IsIso

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}

/-- A morphism of `ℓ`-divisible systems whose components are isomorphisms is an isomorphism. -/
lemma isIso_of_isIso_tower_app {T T' : DivisibleSystem C ℓ} (f : T ⟶ T')
    [∀ m, IsIso (f.tower.app m)] : IsIso f := by
  let g : T' ⟶ T :=
    ⟨{ app := fun m => inv (f.tower.app m)
       naturality := fun _ _ φ => by
         rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
         exact (f.tower.naturality φ).symm },
      fun h => by
        dsimp
        rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
        exact (f.comm h).symm⟩
  refine ⟨g, ?_, ?_⟩
  · ext m
    exact IsIso.hom_inv_id (f.tower.app m)
  · ext m
    exact IsIso.inv_hom_id (f.tower.app m)

end IsIso

section Comparison

variable {A : Type u} [Category.{v} A] [Abelian A] {ℓ : ℕ} (N : ℕ)

/-- An `ℓ`-divisible system of `ℕ`-graded cochain complexes extended by zero to `ℤ`. -/
abbrev extendSystem (K : DivisibleSystem (CochainComplex A ℕ) ℓ) :
    DivisibleSystem (CochainComplex A ℤ) ℓ :=
  K.map (ComplexShape.embeddingUpNat.extendFunctor A)

/-- For `K` vanishing in degrees `q ≥ N`, the comparison from the total complexes, rows `q < N`,
of `K` placed in resolution degree `0` (the target of the Total module's totalized
augmentation) to `K` extended to `ℤ`. -/
def columnTotalSystemComparison (K : DivisibleSystem (CochainComplex A ℕ) ℓ)
    (hK : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) :
    (K.map (columnZero A)).totalSystem N ⟶ K.extendSystem :=
  ⟨{ app := fun m => columnComparison N (K.tower.obj m) (hK m.unop)
     naturality := fun _ _ φ => HomologicalComplex.hom_ext _ _ fun n =>
       columnComparisonF_naturality N (K.tower.map φ) n },
    fun h => HomologicalComplex.hom_ext _ _ fun n =>
      columnComparisonF_naturality N (K.inclusion h) n⟩

lemma columnTotalSystemComparison_tower_app (K : DivisibleSystem (CochainComplex A ℕ) ℓ)
    (hK : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) (m : ℕ) :
    (K.columnTotalSystemComparison N hK).tower.app (Opposite.op m) =
      columnComparison N (K.obj m) (hK m) :=
  rfl

instance isIso_columnTotalSystemComparison (K : DivisibleSystem (CochainComplex A ℕ) ℓ)
    (hK : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) :
    IsIso (K.columnTotalSystemComparison N hK) := by
  have : ∀ m, IsIso ((K.columnTotalSystemComparison N hK).tower.app m) := fun m =>
    isIso_columnComparison N (K.tower.obj m) (hK m.unop)
  exact isIso_of_isIso_tower_app _

/-- `columnTotalSystemComparison` as an isomorphism of `ℓ`-divisible systems. -/
def columnTotalSystemIso (K : DivisibleSystem (CochainComplex A ℕ) ℓ)
    (hK : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) :
    (K.map (columnZero A)).totalSystem N ≅ K.extendSystem :=
  asIso (K.columnTotalSystemComparison N hK)

variable (P : A ⥤ A) (ε : P ⟶ 𝟭 A) [P.Additive] [PreservesFiniteLimits P]
  [PreservesFiniteColimits P]

/-- The totalized augmentation followed by the comparison: a morphism from the total complexes
of the standard resolutions, rows `q < N`, to `K` extended to `ℤ`, for `K` vanishing in degrees
`q ≥ N`. -/
def standardTotalSystemToExtend (K : DivisibleSystem (CochainComplex A ℕ) ℓ)
    (hK : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) :
    K.standardTotalSystem N P ε ⟶ K.extendSystem :=
  K.standardTotalSystemAugmentation N P ε ≫ K.columnTotalSystemComparison N hK

end Comparison

section Group

variable {k : Type u} [CommRing k] {Γ : Type v} [Group Γ] [Finite Γ] {ℓ : ℕ} (N : ℕ)

/-- `standardTotalSystemToExtend` for `P = Ind_1^Γ Res_1^Γ`, `Γ` finite. -/
abbrev groupStandardTotalSystemToExtend
    (K : DivisibleSystem (CochainComplex (Rep.{max w u v} k Γ) ℕ) ℓ)
    (hK : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) :
    K.groupStandardTotalSystem N ⟶ K.extendSystem :=
  K.standardTotalSystemToExtend N (indResBot.{w} k Γ) (indResBotCounit k Γ) hK

end Group

section Smooth

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {ℓ : ℕ}
  (N : ℕ) (K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, max w uR uG} R G) ℕ) ℓ)
  (H : Subgroup G) [H.Normal] [H.FiniteIndex]

/-- The morphism from `quotientInvariantsTotalSystem` to the `H`-invariants system extended to
`ℤ`, for `K` vanishing in degrees `q ≥ N`. -/
abbrev quotientInvariantsTotalSystemToExtend
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))
    (hN : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) :
    K.quotientInvariantsTotalSystem N H hK ⟶ (K.quotientInvariantsComplexes H hK).extendSystem :=
  (K.quotientInvariantsComplexes H hK).groupStandardTotalSystemToExtend N
    (fun m q hq => (smoothQuotientInvariants R H).map_isZero (hN m q hq))

end Smooth

section SmoothGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ) (H : Subgroup G) [H.Normal] [H.FiniteIndex]

/-- The morphism from Harris's `C_m^{•,H}` (`smoothGodementInvariantTotalSystem`) to the
`H`-invariant section complexes extended to `ℤ`: the totalized augmentation followed by the
comparison, whose vanishing hypothesis holds with `N = D + 2`. -/
abbrev smoothGodementInvariantTotalSystemToExtend
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
        ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
        ((smoothGodementResidualSystem h T (D + 1)).projection hm))) :
    smoothGodementInvariantTotalSystem h T D H hterm hres ⟶
      (smoothGodementTruncatedQuotientInvariantSectionsSystem h T D H hterm hres).extendSystem :=
  groupStandardTotalSystemToExtend.{0} (D + 2)
    (smoothGodementTruncatedQuotientInvariantSectionsSystem h T D H hterm hres)
    (fun m _ hq =>
      isZero_smoothGodementTruncatedQuotientInvariantSectionsSystem_obj_X h T D H hterm hres m hq)

end SmoothGodement

end DivisibleSystem

end Langlands.Cohomology
