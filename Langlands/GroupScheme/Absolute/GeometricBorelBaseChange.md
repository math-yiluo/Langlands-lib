# Geometric Borel subgroups under field extension

This is a derived transport result for the existing geometric Borel predicate.
Its ambient group is connected reductive over a field, and the extension is an
arbitrary morphism between spectra of fields in the same universe.

`IsGeometricBorelSubgroup.baseChange` extends the algebraic-closure Borel by the
published `borelAlgClosedFieldExtensionStatement`. The natural comparison between
the two successive pullbacks identifies this inclusion with the
algebraic-closure pullback of the requested inclusion. The published Borel
descent theorem then supplies the Borel property over the extended ground field.
Closedness follows by base change of the original closed inclusion.

The argument uses existing Library theorems and pullback coherence; it introduces
no additional structural result about reductive groups.
