import Langlands.Cohomology.DivisibleSystem.StandardResolution
import Mathlib.Algebra.Homology.Embedding.Restriction
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Total complexes of `ℓ`-divisible systems of double complexes

Harris 1999, §2, p.306, defines `C_m^{•,H}` as the simple complex associated to the double
complex `K_m^{-•,•,H}` of standard resolutions (2.5). This module totalizes the double complexes
of the StandardResolution module.

A double complex here is a cochain complex in `q ∈ ℕ` of chain complexes in `r ∈ ℕ`, with
`P^(r+1)` of the degree `q` term in position `(q, r)`. Its total complex is formed with total
degree `q - r`. This is our indexing convention: with Harris's labels `K^{-(r+1),q}` the same
term has total degree `q - r - 1`, and our convention puts the term `K^{-1,q}` in total degree
`q`. The fiber of `(q, r) ↦ q - r` over a degree is infinite when `q` ranges over `ℕ`, so the rows
are first restricted to `q < N`. The fibers are then finite, the total complex exists in any
abelian category, and totalization is an exact functor. It therefore carries `ℓ`-divisible
systems of double complexes to `ℓ`-divisible systems of `ℤ`-graded cochain complexes.

The augmentation is totalized as well. Its target is the total complex of the system of cochain
complexes placed in resolution degree `0`; this target is not identified with the system of
cochain complexes itself. No quasi-isomorphism, no freeness and no comparison with the
unrestricted rows is proved.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits

universe w v u

section Shape

/-- The cochain complex shape on `Fin N`: differentials `i ⟶ i + 1`. -/
def upFin (N : ℕ) : ComplexShape (Fin N) where
  Rel i j := (i : ℕ) + 1 = j
  next_eq {_ _ _} h h' := Fin.ext (h.symm.trans h')
  prev_eq {_ _ _} h h' := Fin.ext (by omega)

lemma upFin_rel_iff {N : ℕ} (i j : Fin N) : (upFin N).Rel i j ↔ (i : ℕ) + 1 = j :=
  Iff.rfl

/-- The inclusion `Fin N ⊆ ℕ` as an embedding of cochain complex shapes. -/
def upFinEmbedding (N : ℕ) : (upFin N).Embedding (ComplexShape.up ℕ) :=
  ComplexShape.Embedding.mk' _ _ Fin.val Fin.val_injective (fun _ _ => Iff.rfl)

instance (N : ℕ) : (upFinEmbedding N).IsRelIff :=
  ⟨fun _ _ h => h⟩

/-- Totalization of a double complex with rows `q ∈ Fin N` (cochain direction) and columns
`r ∈ ℕ` (chain direction) into a `ℤ`-graded cochain complex, with total degree `q - r`, no sign
on the row differential and the sign `(-1)^q` on the column differential. -/
instance upFinTotalComplexShape (N : ℕ) :
    TotalComplexShape (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) where
  π x := ((x.1 : ℕ) : ℤ) - x.2
  ε₁ _ := 1
  ε₂ x := ((x.1 : ℕ) : ℤ).negOnePow
  rel₁ {q q'} h r := by
    have h' : (q : ℕ) + 1 = q' := h
    simp only [ComplexShape.up_Rel]
    omega
  rel₂ q {r r'} h := by
    have h' : r' + 1 = r := h
    simp only [ComplexShape.up_Rel]
    omega
  ε₂_ε₁ {q q'} _ _ h _ := by
    have h' : (q' : ℕ) = q + 1 := h.symm
    simp only [h', Nat.cast_succ, Int.negOnePow_succ, mul_one, neg_one_mul, neg_neg]

lemma upFin_π {N : ℕ} (q : Fin N) (r : ℕ) :
    ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) =
      ((q : ℕ) : ℤ) - r :=
  rfl

/-- The pairs `(q, r)` of total degree `n`. -/
abbrev upFinFiber (N : ℕ) (n : ℤ) : Set (Fin N × ℕ) :=
  ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) ⁻¹' {n}

/-- Each total degree has finitely many summands: `r` is determined by `q`. -/
instance upFinFiber_finite (N : ℕ) (n : ℤ) : Finite (upFinFiber N n) := by
  refine Finite.of_injective (fun x : upFinFiber N n => x.1.1) ?_
  rintro ⟨⟨q, r⟩, hx⟩ ⟨⟨q', r'⟩, hy⟩ h
  have hx' : ((q : ℕ) : ℤ) - r = n := hx
  have hy' : ((q' : ℕ) : ℤ) - r' = n := hy
  have hq : q = q' := h
  subst hq
  have hr : r = r' := by omega
  subst hr
  rfl

/-- No pair `(q, r)` with `q < N` has total degree `n ≥ N`. -/
lemma upFinFiber_eq_empty {N : ℕ} {n : ℤ} (hn : (N : ℤ) ≤ n) : upFinFiber N n = ∅ := by
  ext ⟨q, r⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, upFin_π, Set.mem_empty_iff_false,
    iff_false]
  have := q.isLt
  omega

end Shape

section Total

variable (A : Type u) [Category.{v} A] [Abelian A] (N : ℕ)

instance hasTotal_upFin (K : HomologicalComplex₂ A (upFin N) (ComplexShape.down ℕ)) :
    K.HasTotal (ComplexShape.up ℤ) :=
  fun _ => inferInstance

/-- The summands of total degree `n` of a double complex with rows `q < N`. -/
@[simps]
def totalSummands (n : ℤ) :
    HomologicalComplex₂ A (upFin N) (ComplexShape.down ℕ) ⥤ (Discrete (upFinFiber N n) ⥤ A) where
  obj K := Discrete.functor (K.toGradedObject.mapObjFun _ n)
  map φ := Discrete.natTrans (fun i => (φ.f i.as.1.1).f i.as.1.2)

/-- Each summand functor is evaluation at the corresponding position. -/
def totalSummandsEvalIso (n : ℤ) (i : upFinFiber N n) :
    totalSummands A N n ⋙ (evaluation _ A).obj ⟨i⟩ ≅
      HomologicalComplex.eval _ (upFin N) i.1.1 ⋙
        HomologicalComplex.eval A (ComplexShape.down ℕ) i.1.2 :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

instance totalSummands_preservesFiniteLimits (n : ℤ) :
    PreservesFiniteLimits (totalSummands A N n) :=
  ⟨fun J _ _ => preservesLimitsOfShape_of_evaluation _ J fun ⟨i⟩ =>
    preservesLimitsOfShape_of_natIso (totalSummandsEvalIso A N n i).symm⟩

instance totalSummands_preservesFiniteColimits (n : ℤ) :
    PreservesFiniteColimits (totalSummands A N n) :=
  ⟨fun J _ _ => preservesColimitsOfShape_of_evaluation _ J fun ⟨i⟩ =>
    preservesColimitsOfShape_of_natIso (totalSummandsEvalIso A N n i).symm⟩

/-- The degree `n` term of the total complex is the coproduct of the summands of total
degree `n`. -/
def totalEvalIso (n : ℤ) :
    HomologicalComplex₂.totalFunctor A (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) ⋙
        HomologicalComplex.eval A (ComplexShape.up ℤ) n ≅
      totalSummands A N n ⋙ colim :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {K L} φ => by
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    refine HomologicalComplex₂.total.hom_ext _ fun q r h => ?_
    exact (HomologicalComplex₂.ιTotal_map _ _ φ (ComplexShape.up ℤ) q r n h).trans
      (colimit.ι_map ((totalSummands A N n).map φ) ⟨⟨(q, r), h⟩⟩).symm)

/-- Totalization of double complexes with rows `q < N` is exact. -/
instance totalFunctor_upFin_preservesFiniteLimits :
    PreservesFiniteLimits
      (HomologicalComplex₂.totalFunctor A (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ)) :=
  ⟨fun J _ _ => HomologicalComplex.preservesLimitsOfShape_of_eval _ fun n => by
    have := Abelian.hasFiniteBiproducts (C := A)
    have : PreservesFiniteLimits (colim : (Discrete (upFinFiber N n) ⥤ A) ⥤ A) :=
      (hasExactColimitsOfShape_discrete_finite A (upFinFiber N n)).preservesFiniteLimits
    exact preservesLimitsOfShape_of_natIso (totalEvalIso A N n).symm⟩

instance totalFunctor_upFin_preservesFiniteColimits :
    PreservesFiniteColimits
      (HomologicalComplex₂.totalFunctor A (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ)) :=
  ⟨fun _ _ _ => HomologicalComplex.preservesColimitsOfShape_of_eval _ fun n =>
    preservesColimitsOfShape_of_natIso (totalEvalIso A N n).symm⟩

instance totalFunctor_upFin_additive :
    (HomologicalComplex₂.totalFunctor A (upFin N) (ComplexShape.down ℕ)
      (ComplexShape.up ℤ)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The total complex vanishes in degrees `n ≥ N`. -/
lemma isZero_total_X (K : HomologicalComplex₂ A (upFin N) (ComplexShape.down ℕ)) {n : ℤ}
    (hn : (N : ℤ) ≤ n) : IsZero ((K.total (ComplexShape.up ℤ)).X n) := by
  rw [IsZero.iff_id_eq_zero]
  refine HomologicalComplex₂.total.hom_ext _ fun q r h => ?_
  have hmem : (q, r) ∈ upFinFiber N n := h
  rw [upFinFiber_eq_empty hn] at hmem
  exact hmem.elim

/-- Restricting the outer index of a double complex to `q < N` is evaluation in each degree. -/
def upFinRestrictionEvalIso (q : Fin N) :
    (upFinEmbedding N).restrictionFunctor (HomologicalComplex A (ComplexShape.down ℕ)) ⋙
        HomologicalComplex.eval _ (upFin N) q ≅
      HomologicalComplex.eval _ (ComplexShape.up ℕ) (q : ℕ) :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

instance upFinRestriction_preservesFiniteLimits :
    PreservesFiniteLimits
      ((upFinEmbedding N).restrictionFunctor (HomologicalComplex A (ComplexShape.down ℕ))) :=
  ⟨fun _ _ _ => HomologicalComplex.preservesLimitsOfShape_of_eval _ fun q =>
    preservesLimitsOfShape_of_natIso (upFinRestrictionEvalIso A N q).symm⟩

instance upFinRestriction_preservesFiniteColimits :
    PreservesFiniteColimits
      ((upFinEmbedding N).restrictionFunctor (HomologicalComplex A (ComplexShape.down ℕ))) :=
  ⟨fun _ _ _ => HomologicalComplex.preservesColimitsOfShape_of_eval _ fun q =>
    preservesColimitsOfShape_of_natIso (upFinRestrictionEvalIso A N q).symm⟩

/-- Restriction of the rows to `q < N` followed by totalization with total degree `q - r`. -/
abbrev upFinTotalFunctor :
    HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.down ℕ) ⥤ CochainComplex A ℤ :=
  (upFinEmbedding N).restrictionFunctor (HomologicalComplex A (ComplexShape.down ℕ)) ⋙
    HomologicalComplex₂.totalFunctor A (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ)

/-- The summand inclusion of position `(q, r)`, `q < N`, into the degree `q - r` term. -/
abbrev upFinTotalι (K : HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.down ℕ))
    (q : Fin N) (r : ℕ) :
    (K.X q).X r ⟶ ((upFinTotalFunctor A N).obj K).X (((q : ℕ) : ℤ) - r) :=
  HomologicalComplex₂.ιTotal (((upFinEmbedding N).restrictionFunctor _).obj K)
    (ComplexShape.up ℤ) q r _ rfl

lemma isZero_upFinTotalFunctor_obj_X
    (K : HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.down ℕ)) {n : ℤ}
    (hn : (N : ℤ) ≤ n) : IsZero (((upFinTotalFunctor A N).obj K).X n) :=
  isZero_total_X A N _ hn

end Total

namespace DivisibleSystem

section Total

variable {A : Type u} [Category.{v} A] [Abelian A] {ℓ : ℕ} (N : ℕ)

/-- The total complexes, with rows restricted to `q < N` and total degree `q - r`, of an
`ℓ`-divisible system of double complexes. -/
abbrev totalSystem (K : DivisibleSystem
    (HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.down ℕ)) ℓ) :
    DivisibleSystem (CochainComplex A ℤ) ℓ :=
  K.map (upFinTotalFunctor A N)

/-- The morphism of total systems induced by a morphism of systems of double complexes. -/
abbrev totalSystemMap {K K' : DivisibleSystem
    (HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.down ℕ)) ℓ} (f : K ⟶ K') :
    K.totalSystem N ⟶ K'.totalSystem N :=
  (mapFunctor _ ℓ (upFinTotalFunctor A N)).map f

lemma isZero_totalSystem_obj_X (K : DivisibleSystem
    (HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.down ℕ)) ℓ) (m : ℕ) {n : ℤ}
    (hn : (N : ℤ) ≤ n) : IsZero (((K.totalSystem N).obj m).X n) :=
  isZero_upFinTotalFunctor_obj_X A N _ hn

variable (P : A ⥤ A) (ε : P ⟶ 𝟭 A) [P.Additive] [PreservesFiniteLimits P]
  [PreservesFiniteColimits P]

/-- The total complexes of the standard resolutions of an `ℓ`-divisible system of `ℕ`-graded
cochain complexes, rows restricted to `q < N`: at level `m`, the degree `n` term is the
coproduct of the `P^(r+1)` of the degree `q` terms over `q - r = n`, `q < N` (Harris's
`C_m^{•,H}` of p.306, with total degree `q - r` in place of the literal `q - r - 1`). -/
abbrev standardTotalSystem (K : DivisibleSystem (CochainComplex A ℕ) ℓ) :
    DivisibleSystem (CochainComplex A ℤ) ℓ :=
  (K.standardResolutionDoubleComplexes P ε).totalSystem N

/-- The summand inclusion `P^(r+1) (K_m^q) ⟶ C_m^(q-r)` for `q < N`. -/
abbrev standardTotalSystemι (K : DivisibleSystem (CochainComplex A ℕ) ℓ) (m : ℕ) (q : Fin N)
    (r : ℕ) :
    (standardPow P (r + 1)).obj ((K.obj m).X q) ⟶
      ((K.standardTotalSystem N P ε).obj m).X (((q : ℕ) : ℤ) - r) :=
  upFinTotalι A N ((K.standardResolutionDoubleComplexes P ε).obj m) q r

/-- The totalized augmentation. Its target is the total complex (rows `q < N`) of the system of
cochain complexes placed in resolution degree `0`, not the system of cochain complexes itself. -/
abbrev standardTotalSystemAugmentation (K : DivisibleSystem (CochainComplex A ℕ) ℓ) :
    K.standardTotalSystem N P ε ⟶
      (K.map ((ChainComplex.single₀ A).mapHomologicalComplex
        (ComplexShape.up ℕ))).totalSystem N :=
  totalSystemMap N (K.standardResolutionDoubleComplexesAugmentation P ε)

end Total

section Group

variable {k : Type u} [CommRing k] {Γ : Type v} [Group Γ] [Finite Γ] {ℓ : ℕ} (N : ℕ)

/-- The total complexes, rows restricted to `q < N`, of the standard resolutions along
`Ind_1^Γ Res_1^Γ` of an `ℓ`-divisible system of cochain complexes of representations of a finite
group. -/
abbrev groupStandardTotalSystem
    (K : DivisibleSystem (CochainComplex (Rep.{max w u v} k Γ) ℕ) ℓ) :
    DivisibleSystem (CochainComplex (Rep.{max w u v} k Γ) ℤ) ℓ :=
  K.standardTotalSystem N (indResBot.{w} k Γ) (indResBotCounit k Γ)

/-- The totalized augmentation of `groupStandardTotalSystem`. -/
abbrev groupStandardTotalSystemAugmentation
    (K : DivisibleSystem (CochainComplex (Rep.{max w u v} k Γ) ℕ) ℓ) :
    K.groupStandardTotalSystem N ⟶
      (K.map ((ChainComplex.single₀ (Rep.{max w u v} k Γ)).mapHomologicalComplex
        (ComplexShape.up ℕ))).totalSystem N :=
  K.standardTotalSystemAugmentation N (indResBot.{w} k Γ) (indResBotCounit k Γ)

end Group

end DivisibleSystem

end Langlands.Cohomology
