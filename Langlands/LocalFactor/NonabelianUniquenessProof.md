# Uniqueness of common-closure local-constant systems

`Langlands.LocalFactor.NonabelianSystem.unique` proves the existing proposition
`NonabelianSystem.Unique.{uF,uV} F e` for every prime `p`, finite p-adic field
`F : PadicField.{uF} p`, and supplied reciprocity family `e`. The field universe
`uF` and representation-carrier universe `uV` are independent. The assignments
have the existing continuous exact virtual groups with carrier universe
`max uF uV` as their virtual inputs. Any two assignments satisfying
`NonabelianSystem.IsSystem F e` are equal as functions.

The implemented proof applies
`NonabelianSystem.unique_of_commonClosureDegreeZeroGeneration` to the published
theorem `commonClosureDegreeZeroGeneration.{uF,uV} p F`. That theorem supplies
generation of the actual dimension-zero kernel at every finite intermediate
field by the integer span of exact inductions of differences of continuous
character lines from nested intermediate fields. The generation premise of the
reduction is therefore discharged by a theorem.

The imported reduction compares the systems on all continuous character lines
using abelianization descent and the same supplied reciprocity family. Their
degree-zero induction laws transfer this comparison to the induced character
differences, using the actual field-trace additive character and a constructed
source Haar measure. Additivity extends the equality to the integer span.
Generation identifies that span with the dimension-zero kernel. Every virtual
class is its dimension-zero part plus its integer degree times the trivial
character class, on which rank-one agreement also compares the systems.
Function extensionality then gives equality of the assignments. These steps are
implemented in the imported reduction; this module supplies its proved premise.
The second theorem, `Langlands.LocalFactor.nonabelianSystemUniqueness`, applies
the first uniformly to prove `NonabelianSystemUniquenessStatement.{uF,uV}`.

This is an internal assembly of the published generation and uniqueness
reduction. Its mathematical provenance is Tate, *Number theoretic background*
(1979), (2.3.1)–(2.3.3), printed pages 11–12, retained Part II PDF pages 20–21:
degree-zero induction and the values on quasicharacters determine an additive
family. Registered source: `tate-1979-number-theoretic-background`, SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The existing statement modules document the common-closure presentation and
its specialization to finite extensions of `Q_p`.

The result is uniqueness for the same supplied family in the specified common
closure. It has no generation, Brauer, existence, or comparison premise and
selects no system or reciprocity family. Existence and comparison between
different families, fields, closures, or carrier universes remain separate
claims.
